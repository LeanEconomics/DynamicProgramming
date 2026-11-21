/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-!
# The g.c.d. of a set of return times

Copied from `StochasticStability/DriftRegularity` (module `Period`, the g.c.d. part of
Meyn–Tweedie §5.4 and Lemma D.7.4), with names prefixed `mc_`. Used for the period of a state
(Miao, Definition 3.1.4, p. 93), Theorem 3.1.2 (p. 93) and the number-theory lemma in the proof
of Theorem 3.1.4 (p. 96; Billingsley, Appendix A21).

* `mc_IsAddClosed S`: `S ⊆ ℕ` is closed under addition; `mc_setGcd S`: the largest common
  divisor of the elements of `S` (`0` when `S` has no positive element).
* `mc_setGcd_dvd`, `dvd_mc_setGcd`, `mc_setGcd_pos`: for additively closed `S` with a positive
  element, `mc_setGcd S` divides every element and every common divisor divides it.
* `mc_eventually_mul_setGcd_mem`: such an `S` contains every large multiple of its g.c.d.;
  `mc_eventually_mem_of_setGcd_eq_one`: if the g.c.d. is `1`, `S` contains all large integers.
-/

namespace Miao.MarkovProcesses

/-- `S ⊆ ℕ` is closed under addition. -/
def mc_IsAddClosed (S : Set ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S

/-- The **greatest common divisor** of `S ⊆ ℕ`: the largest common divisor of its elements
(the period of Miao, Definition 3.1.4, p. 93). -/
noncomputable def mc_setGcd (S : Set ℕ) : ℕ := sSup {d | ∀ s ∈ S, d ∣ s}

/-- Multiples `(q + 1) b` of an element of an additively closed set lie in it. -/
theorem mc_IsAddClosed.succ_mul_mem {S : Set ℕ} (hS : mc_IsAddClosed S) {b : ℕ} (hb : b ∈ S)
    (q : ℕ) :
    (q + 1) * b ∈ S := by
  induction q with
  | zero => simpa using hb
  | succ q ih => rw [add_mul, one_mul]; exact hS _ ih _ hb

/-- Multiples `q b` of an element of `S ∪ {0}` lie in `S ∪ {0}`. -/
theorem mc_IsAddClosed.mul_mem_zero {S : Set ℕ} (hS : mc_IsAddClosed S) {b : ℕ} (hb : b = 0 ∨ b ∈ S)
    (q : ℕ) : q * b = 0 ∨ q * b ∈ S := by
  rcases hb with rfl | hb
  · left; simp
  · rcases q with _ | q
    · left; simp
    · exact Or.inr (hS.succ_mul_mem hb q)

/-- The sum of an element of `S ∪ {0}` and an element of `S` lies in `S`. -/
theorem mc_IsAddClosed.add_mem_of_zero {S : Set ℕ} (hS : mc_IsAddClosed S) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
  rcases ha with rfl | ha
  · simpa using hb
  · exact hS _ ha _ hb

/-- **The g.c.d. as a least difference.** If `S` is additively closed and has a positive element,
the least positive difference `g = b − a` of elements of `S ∪ {0}` (with `b ∈ S`) divides every
element of `S`, and every common divisor of `S` divides it. -/
theorem mc_exists_gcd_witness {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
    (hpos : 0 < s₀) :
    ∃ g a, 0 < g ∧ (a = 0 ∨ a ∈ S) ∧ a + g ∈ S ∧ (∀ s ∈ S, g ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ g := by
  set T : Set ℕ := {g | 0 < g ∧ ∃ a, (a = 0 ∨ a ∈ S) ∧ a + g ∈ S} with hT
  have hTne : T.Nonempty := ⟨s₀, hpos, 0, Or.inl rfl, by simpa using hs₀⟩
  obtain ⟨hgpos, a, ha, hag⟩ := Nat.sInf_mem hTne
  set g := sInf T
  refine ⟨g, a, hgpos, ha, hag, fun s hs => ?_, fun d hd => ?_⟩
  · -- the remainder of `s` modulo `g` is a smaller positive difference unless it is `0`
    by_contra hdvd
    have hr : 0 < s % g := Nat.pos_of_ne_zero fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hrT : s % g ∈ T := by
      refine ⟨hr, s / g * (a + g), hS.mul_mem_zero (Or.inr hag) _, ?_⟩
      have hsplit : s / g * (a + g) + s % g = s / g * a + s := by
        have := Nat.div_add_mod s g
        nlinarith [this]
      rw [hsplit]
      exact hS.add_mem_of_zero (hS.mul_mem_zero ha _) hs
    exact absurd (Nat.sInf_le hrT) (not_le.2 (Nat.mod_lt s hgpos))
  · have h1 : d ∣ a := by
      rcases ha with rfl | ha
      · exact dvd_zero d
      · exact hd a ha
    exact (Nat.dvd_add_right h1).1 (hd _ hag)

/-- For an additively closed `S` with a positive element, `mc_setGcd S` is the least positive
difference of `mc_exists_gcd_witness`. -/
theorem mc_setGcd_spec {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ a, 0 < mc_setGcd S ∧ (a = 0 ∨ a ∈ S) ∧ a + mc_setGcd S ∈ S ∧ (∀ s ∈ S, mc_setGcd S ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ mc_setGcd S := by
  obtain ⟨g, a, hg, ha, hag, hdvd, hmax⟩ := mc_exists_gcd_witness hS hs₀ hpos
  have heq : mc_setGcd S = g := by
    refine IsGreatest.csSup_eq ⟨hdvd, fun d hd => Nat.le_of_dvd hg (hmax d hd)⟩
  rw [heq]
  exact ⟨a, hg, ha, hag, hdvd, hmax⟩

/-- `mc_setGcd S` divides every element of `S`. -/
theorem mc_setGcd_dvd {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {s : ℕ} (hs : s ∈ S) : mc_setGcd S ∣ s := by
  obtain ⟨a, -, -, -, h, -⟩ := mc_setGcd_spec hS hs₀ hpos
  exact h s hs

/-- Every common divisor of `S` divides `mc_setGcd S`. -/
theorem dvd_mc_setGcd {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {d : ℕ} (hd : ∀ s ∈ S, d ∣ s) : d ∣ mc_setGcd S := by
  obtain ⟨a, -, -, -, -, h⟩ := mc_setGcd_spec hS hs₀ hpos
  exact h d hd

/-- `mc_setGcd S > 0`. -/
theorem mc_setGcd_pos {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    0 < mc_setGcd S := by
  obtain ⟨a, h, -⟩ := mc_setGcd_spec hS hs₀ hpos
  exact h

/-- An additively closed set of naturals with a positive
element contains every large enough multiple of its g.c.d. -/
theorem mc_eventually_mul_setGcd_mem {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
    (hpos : 0 < s₀) :
    ∃ N, ∀ n ≥ N, n * mc_setGcd S ∈ S := by
  obtain ⟨a, hg, ha, hag, hdvd, -⟩ := mc_setGcd_spec hS hs₀ hpos
  set g := mc_setGcd S
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact hS.succ_mul_mem (by simpa using hag) q
  · have haS : a ∈ S := ha.resolve_left ha0
    obtain ⟨k, hk⟩ := hdvd a haS
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => ha0 (by rw [hk, h, mul_zero])
    refine ⟨k * k, fun n hn => ?_⟩
    have hx : k ≤ n / k := (Nat.le_div_iff_mul_le hk0).2 hn
    have hr : n % k < k := Nat.mod_lt n hk0
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt (hr.trans_le hx)
    -- `n g = (t + 1) a + (n % k) (a + g)`
    have hsplit : n * g = (t + 1) * a + n % k * (a + g) := by
      have h1 := Nat.div_add_mod n k
      rw [ht] at h1
      rw [hk]
      nlinarith [h1]
    rw [hsplit]
    rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
    · rw [h0, zero_mul, add_zero]; exact hS.succ_mul_mem haS t
    · obtain ⟨r, hr'⟩ := Nat.exists_eq_add_of_lt h0
      rw [hr', zero_add]
      exact hS _ (hS.succ_mul_mem haS t) _ (hS.succ_mul_mem hag r)

/-- An additively closed set of naturals with a positive element and g.c.d. `1` contains every
large enough natural number (the lemma of Billingsley, Appendix A21, quoted in Miao, p. 96). -/
theorem mc_eventually_mem_of_setGcd_eq_one {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ}
    (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) (h1 : mc_setGcd S = 1) : ∃ N, ∀ n ≥ N, n ∈ S := by
  obtain ⟨N, hN⟩ := mc_eventually_mul_setGcd_mem hS hs₀ hpos
  exact ⟨N, fun n hn => by simpa [h1] using hN n hn⟩

/-- The argument of Theorem 3.1.2 (Miao, p. 93) on sets of times: if `n > 0` lies in two
additively closed sets `R₁`, `R₂`, and adding `n` maps each into the other, then the two sets
have the same g.c.d. -/
theorem mc_setGcd_eq_of_shift {R₁ R₂ : Set ℕ} (h₁ : mc_IsAddClosed R₁) (h₂ : mc_IsAddClosed R₂)
    {n : ℕ} (hn : 0 < n) (hn₁ : n ∈ R₁) (hn₂ : n ∈ R₂) (h12 : ∀ t ∈ R₂, n + t ∈ R₁)
    (h21 : ∀ t ∈ R₁, n + t ∈ R₂) : mc_setGcd R₁ = mc_setGcd R₂ := by
  apply Nat.dvd_antisymm
  · refine dvd_mc_setGcd h₂ hn₂ hn fun t ht => ?_
    exact (Nat.dvd_add_right (mc_setGcd_dvd h₁ hn₁ hn hn₁)).1 (mc_setGcd_dvd h₁ hn₁ hn (h12 t ht))
  · refine dvd_mc_setGcd h₁ hn₁ hn fun t ht => ?_
    exact (Nat.dvd_add_right (mc_setGcd_dvd h₂ hn₂ hn hn₂)).1 (mc_setGcd_dvd h₂ hn₂ hn (h21 t ht))

end Miao.MarkovProcesses

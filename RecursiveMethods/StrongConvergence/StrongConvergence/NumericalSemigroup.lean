/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Sets of natural numbers closed under addition

A set `R ⊆ ℕ` closed under addition, containing a positive element, whose elements have no
common divisor other than `1`, contains every sufficiently large integer
(`eventually_mem_of_add_closed`). This is the number theory behind aperiodicity in Theorem
11.4: the return times of a state form such a set.

The proof: call `d > 0` *big* if `R` contains all large multiples of `d`. Each positive `r ∈ R`
is big. If `d` is big and `r ∈ R`, then `gcd(d, r)` is big, by the Chicken McNugget theorem
(`frobeniusNumber_pair`) applied to `d/g` and `r/g`. So the least big `d` divides every element
of `R`, and is `1`.
-/

namespace StokeyLucasPrescott.StrongConvergence

/-- Coprime `a, b ≥ 1`: every `s ≥ ab` is `xa + yb` with `x, y ∈ ℕ`. -/
theorem exists_nonneg_comb {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) {s : ℕ}
    (hs : a * b ≤ s) : ∃ x y : ℕ, x * a + y * b = s := by
  rcases Nat.lt_or_ge 1 a with ha1 | ha1
  · rcases Nat.lt_or_ge 1 b with hb1 | hb1
    · have hab1 : 1 ≤ a * b := Nat.mul_pos ha hb
      have hF := (frobeniusNumber_iff.1 (frobeniusNumber_pair hab ha1 hb1)).2 s (by omega)
      obtain ⟨x, y, h⟩ := (AddSubmonoid.mem_closure_pair a b s).1 hF
      exact ⟨x, y, by simpa [smul_eq_mul] using h⟩
    · exact ⟨0, s, by rw [show b = 1 by omega]; ring⟩
  · exact ⟨s, 0, by rw [show a = 1 by omega]; ring⟩

/-- `d > 0` is **big** for `R` if `R` contains all large multiples of `d`. -/
def BigFor (R : Set ℕ) (d : ℕ) : Prop := 0 < d ∧ ∃ n₀, ∀ n ≥ n₀, n * d ∈ R

theorem nsmul_mem {R : Set ℕ} (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R) {r : ℕ} (hr : r ∈ R) :
    ∀ n, 1 ≤ n → n * r ∈ R := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using hr
    · rw [Nat.succ_mul]; exact hadd _ (ih hpos) _ hr

theorem bigFor_gcd {R : Set ℕ} (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R) {d r : ℕ}
    (hd : BigFor R d) (hr : r ∈ R) (hr0 : 0 < r) : BigFor R (Nat.gcd d r) := by
  obtain ⟨hd0, n₀, hn₀⟩ := hd
  set g := Nat.gcd d r
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hd0
  set d' := d / g
  set r' := r / g
  have hd' : d = d' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left d r)).symm
  have hr' : r = r' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right d r)).symm
  have hd'0 : 0 < d' := Nat.div_pos (Nat.gcd_le_left r hd0) hg
  have hr'0 : 0 < r' := Nat.div_pos (Nat.gcd_le_right (m := d) hr0) hg
  have hcop : Nat.Coprime d' r' := Nat.coprime_div_gcd_div_gcd hg
  refine ⟨hg, (n₀ + 1) * d' + d' * r', fun t ht => ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_nonneg_comb hcop hd'0 hr'0
    (s := t - (n₀ + 1) * d') (by omega)
  have ht' : t * g = (n₀ + 1 + x) * d + y * r := by
    have : t = (n₀ + 1 + x) * d' + y * r' := by
      have := Nat.sub_add_cancel (show (n₀ + 1) * d' ≤ t by omega)
      rw [← this, ← hxy]; ring
    rw [this, hd', hr']; ring
  rw [ht']
  have h1 : (n₀ + 1 + x) * d ∈ R := hn₀ _ (by omega)
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simpa using h1
  · exact hadd _ h1 _ (nsmul_mem hadd hr y hy)

/-- A set of naturals closed under addition, with a positive element and no common divisor
other than `1`, contains all sufficiently large naturals. -/
theorem eventually_mem_of_add_closed {R : Set ℕ} (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R)
    (hne : ∃ a ∈ R, 0 < a) (hgcd : ∀ d, (∀ n ∈ R, d ∣ n) → d = 1) :
    ∃ n₀, ∀ n ≥ n₀, n ∈ R := by
  classical
  obtain ⟨a, ha, ha0⟩ := hne
  have hex : ∃ d, BigFor R d := ⟨a, ha0, 1, fun n hn => nsmul_mem hadd ha n hn⟩
  set d₀ := Nat.find hex
  have hd₀ : BigFor R d₀ := Nat.find_spec hex
  have hdvd : ∀ n ∈ R, d₀ ∣ n := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact dvd_zero _
    · have hb := bigFor_gcd hadd hd₀ hr hr0
      have hle : d₀ ≤ Nat.gcd d₀ r := Nat.find_min' hex hb
      have hge : Nat.gcd d₀ r ≤ d₀ := Nat.gcd_le_left r hd₀.1
      have : Nat.gcd d₀ r = d₀ := le_antisymm hge hle
      rw [← this]; exact Nat.gcd_dvd_right d₀ r
  have h1 := hgcd d₀ hdvd
  obtain ⟨-, n₀, hn₀⟩ := hd₀
  refine ⟨n₀, fun n hn => ?_⟩
  have := hn₀ n hn
  rwa [h1, mul_one] at this

end StokeyLucasPrescott.StrongConvergence

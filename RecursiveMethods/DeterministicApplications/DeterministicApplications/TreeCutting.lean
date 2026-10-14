/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# A tree-cutting problem

SLP §5.5, p. 107: a tree of size `k_t` grows to `k_{t+1} = h(k_t)`; wood sells at `p = 1`, and
`β = 1/(1 + r)`. Exercise 5.5 is open-ended ("under what assumptions about `h` is there a simple
rule"); the answers here are the monotone (one-step look-ahead) rules.

Both parts are optimal stopping problems along `k_t = hᵗ(k₀)`. Cutting at `T` when the land
left behind is worth `L` pays `P(T) = βᵀ(k_T + L)`, and
`P(T + 1) − P(T) = βᵀ[βh(k_T) − k_T − (1 − β)L]`. Let `S_L = {k : βh(k) − k ≤ (1 − β)L}`.

* `first_entry_optimal`: if the path stays in `S_L` once it has entered (an `h`-invariant
  `S' ⊆ S_L`), the first entry time maximizes `P`. `never_entry_strictMono`: if the path never
  enters `S_L`, `P` increases forever and no cutting time is optimal.
* **Exercise 5.5a** (no replanting, `L = 0`): `ex_5_5a`: cut at the first `t` with
  `h(k_t)/k_t ≤ 1 + r`. This is optimal when trees grow (`h(k) ≥ k`) and the growth factor
  `h(k)/k` does not rise with size (`ratio_invariant`). `treeValue` solves the functional
  equation `v(k) = max{k, βv(h(k))}` (`treeValue_fe`), and is the largest payoff
  (`le_treeValue`).
* **Exercise 5.5b** (replanting at cost `c` with a sapling of size `s`): the stationary rotation
  of length `T` has land value `L(T) = (βᵀk_T − c)/(1 − βᵀ)` (Faustmann; `faustmann_identity`);
  the best rotation value `L*` solves `L = max_{T ≥ 1} βᵀ(k_T + L) − c` (`faustmann_fe`); and
  `ex_5_5b`: cut when `βh(k) − k ≤ (1 − β)L*` (the one-period gain from waiting no longer covers
  the rent on the land). This rule gives an optimal rotation when the gain `βh(k) − k` falls
  with size past some `k₁` (`antitone_invariant`).
-/

open Set

namespace StokeyLucasPrescott.DeterministicApplications

variable {h : ℝ → ℝ} {β L : ℝ}

/-- The payoff `βᵀ(k_T + L)` from cutting at `T`, `k_T = hᵀ(k₀)`. -/
noncomputable def cutPayoff (h : ℝ → ℝ) (β L k₀ : ℝ) (T : ℕ) : ℝ := β ^ T * (h^[T] k₀ + L)

/-- `S_L = {k : βh(k) − k ≤ (1 − β)L}`: waiting one more period does not pay. -/
def stopSet (h : ℝ → ℝ) (β L : ℝ) : Set ℝ := {k | β * h k - k ≤ (1 - β) * L}

theorem cutPayoff_succ (k₀ : ℝ) (T : ℕ) :
    cutPayoff h β L k₀ (T + 1) - cutPayoff h β L k₀ T =
      β ^ T * (β * h (h^[T] k₀) - h^[T] k₀ - (1 - β) * L) := by
  simp only [cutPayoff, Function.iterate_succ_apply', pow_succ]
  ring

/-- **The monotone rule.** If the path enters an `h`-invariant subset `S'` of `S_L` at `T*` and
lies outside `S_L` before, cutting at `T*` is optimal. -/
theorem first_entry_optimal (hβ : 0 < β) {S' : Set ℝ} (hS' : S' ⊆ stopSet h β L)
    (hinv : MapsTo h S' S') {k₀ : ℝ} {Tstar : ℕ} (hin : h^[Tstar] k₀ ∈ S')
    (hbefore : ∀ t < Tstar, h^[t] k₀ ∉ stopSet h β L) (T : ℕ) :
    cutPayoff h β L k₀ T ≤ cutPayoff h β L k₀ Tstar := by
  -- the payoff rises before `T*`
  have hup : ∀ t < Tstar, cutPayoff h β L k₀ t < cutPayoff h β L k₀ (t + 1) := fun t ht => by
    have := cutPayoff_succ (h := h) (β := β) (L := L) k₀ t
    have hns := hbefore t ht
    simp only [stopSet, mem_ofPred_eq, not_le] at hns
    have : 0 < β ^ t * (β * h (h^[t] k₀) - h^[t] k₀ - (1 - β) * L) :=
      mul_pos (pow_pos hβ t) (by linarith)
    linarith
  -- and falls after it
  have hstay : ∀ n, h^[Tstar + n] k₀ ∈ S' := fun n => by
    induction n with
    | zero => simpa using hin
    | succ n ih =>
      rw [← add_assoc, Function.iterate_succ_apply']
      exact hinv ih
  have hdown : ∀ n, cutPayoff h β L k₀ (Tstar + n + 1) ≤ cutPayoff h β L k₀ (Tstar + n) :=
    fun n => by
      have := cutPayoff_succ (h := h) (β := β) (L := L) k₀ (Tstar + n)
      have hs : β * h (h^[Tstar + n] k₀) - h^[Tstar + n] k₀ ≤ (1 - β) * L := hS' (hstay n)
      have : β ^ (Tstar + n) * (β * h (h^[Tstar + n] k₀) - h^[Tstar + n] k₀ - (1 - β) * L)
          ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le _) (by linarith)
      linarith
  have hleft : ∀ d : ℕ, ∀ T, T + d = Tstar → cutPayoff h β L k₀ T ≤ cutPayoff h β L k₀ Tstar := by
    intro d
    induction d with
    | zero =>
      intro T hT
      obtain rfl : T = Tstar := by omega
      exact le_rfl
    | succ d ih =>
      intro T hT
      exact (hup T (by omega)).le.trans (ih (T + 1) (by omega))
  have hright : ∀ n, cutPayoff h β L k₀ (Tstar + n) ≤ cutPayoff h β L k₀ Tstar := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (hdown n).trans ih
  rcases le_total T Tstar with hT | hT
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hT
    exact hleft d T hd.symm
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hright n

/-- If the path never enters `S_L`, the payoff increases forever: no cutting time is optimal. -/
theorem never_entry_strictMono (hβ : 0 < β) {k₀ : ℝ} (hnever : ∀ t, h^[t] k₀ ∉ stopSet h β L) :
    StrictMono (cutPayoff h β L k₀) := by
  refine strictMono_nat_of_lt_succ fun t => ?_
  have := cutPayoff_succ (h := h) (β := β) (L := L) k₀ t
  have hns := hnever t
  simp only [stopSet, mem_ofPred_eq, not_le] at hns
  have : 0 < β ^ t * (β * h (h^[t] k₀) - h^[t] k₀ - (1 - β) * L) :=
    mul_pos (pow_pos hβ t) (by linarith)
  linarith

/-! ### Exercise 5.5a: no replanting -/

/-- If trees grow and the growth factor `h(k)/k` does not rise with size, then the positive
part of `S_0 = {k : βh(k) ≤ k}` is `h`-invariant. -/
theorem ratio_invariant (hβ : 0 < β) (hgrow : ∀ k, 0 < k → k ≤ h k)
    (hratio : ∀ a b, 0 < a → a ≤ b → h b * a ≤ h a * b) :
    MapsTo h (stopSet h β 0 ∩ Ioi 0) (stopSet h β 0 ∩ Ioi 0) := by
  rintro k ⟨hk, hk0⟩
  have hk0' : 0 < k := hk0
  have hkh := hgrow k hk0'
  have hb : 0 < h k := hk0'.trans_le hkh
  refine ⟨?_, hb⟩
  simp only [stopSet, mem_ofPred_eq, mul_zero] at hk ⊢
  have h1 := hratio k (h k) hk0' hkh
  have h2 : β * h (h k) * k ≤ β * h k * h k := by
    have := mul_le_mul_of_nonneg_left h1 hβ.le; linarith
  have h3 : β * h k * h k ≤ k * h k := mul_le_mul_of_nonneg_right (by linarith) hb.le
  nlinarith

/-- **Exercise 5.5a.** Under `ratio_invariant`'s assumptions the rule "cut at the first `t` with
`βh(k_t) ≤ k_t`, i.e. `h(k_t)/k_t ≤ 1 + r`" is optimal. -/
theorem ex_5_5a (hβ : 0 < β) (hgrow : ∀ k, 0 < k → k ≤ h k)
    (hratio : ∀ a b, 0 < a → a ≤ b → h b * a ≤ h a * b) {k₀ : ℝ} (hk₀ : 0 < k₀) {Tstar : ℕ}
    (hin : β * h (h^[Tstar] k₀) ≤ h^[Tstar] k₀)
    (hbefore : ∀ t < Tstar, h^[t] k₀ < β * h (h^[t] k₀)) (T : ℕ) :
    β ^ T * h^[T] k₀ ≤ β ^ Tstar * h^[Tstar] k₀ := by
  have hpos : ∀ t, 0 < h^[t] k₀ := fun t => by
    induction t with
    | zero => simpa using hk₀
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans_le (hgrow _ ih)
  have := first_entry_optimal (L := 0) hβ inter_subset_left (ratio_invariant hβ hgrow hratio)
    ⟨show β * h (h^[Tstar] k₀) - h^[Tstar] k₀ ≤ (1 - β) * 0 by linarith, hpos Tstar⟩
    (fun t ht hs => by
      have := hbefore t ht
      simp only [stopSet, mem_ofPred_eq, mul_zero] at hs
      linarith) T
  simpa [cutPayoff] using this

/-- When every path reaches `S_0`, cut at the first entry: `v(k) = βᵀ*k_{T*}`. -/
noncomputable def treeValue (h : ℝ → ℝ) (β : ℝ)
    (hreach : ∀ k, ∃ t, h^[t] k ∈ stopSet h β 0) (k : ℝ) : ℝ :=
  by classical exact cutPayoff h β 0 k (Nat.find (hreach k))

/-- **Exercise 5.5a.** `treeValue` solves `v(k) = max{k, βv(h(k))}` when `S_0` is invariant. -/
theorem treeValue_fe (hβ : 0 < β) (hinv : MapsTo h (stopSet h β 0) (stopSet h β 0))
    (hreach : ∀ k, ∃ t, h^[t] k ∈ stopSet h β 0) (k : ℝ) :
    treeValue h β hreach k = max k (β * treeValue h β hreach (h k)) := by
  classical
  simp only [treeValue]
  by_cases hk : k ∈ stopSet h β 0
  · -- cut now: `T*(k) = 0`, and `T*(h k) = 0` too
    have h0 : Nat.find (hreach k) = 0 := (Nat.find_eq_zero _).2 (by simpa using hk)
    have h1 : Nat.find (hreach (h k)) = 0 := (Nat.find_eq_zero _).2 (by simpa using hinv hk)
    rw [h0, h1]
    simp only [stopSet, mem_ofPred_eq, mul_zero] at hk
    simp only [cutPayoff, pow_zero, Function.iterate_zero, id_eq, add_zero, one_mul]
    rw [max_eq_left (by linarith)]
  · -- wait: `T*(k) = T*(h k) + 1`
    have hpos : Nat.find (hreach k) ≠ 0 := fun he => hk (by
      have := Nat.find_spec (hreach k); rwa [he] at this)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hfind : Nat.find (hreach (h k)) = n := by
      rw [Nat.find_eq_iff]
      constructor
      · have := Nat.find_spec (hreach k)
        rwa [hn, Function.iterate_succ_apply] at this
      · intro m hm hmem
        have := Nat.find_min (hreach k) (show m + 1 < Nat.find (hreach k) by omega)
        exact this (by rwa [Function.iterate_succ_apply])
    rw [hn, hfind]
    have hval : cutPayoff h β 0 k (n + 1) = β * cutPayoff h β 0 (h k) n := by
      simp only [cutPayoff, Function.iterate_succ_apply, pow_succ]
      ring
    rw [hval]
    simp only [stopSet, mem_ofPred_eq, mul_zero, not_le] at hk
    -- waiting beats cutting: `βv(h k) ≥ βh(k) > k`
    have hge : cutPayoff h β 0 (h k) 0 ≤ cutPayoff h β 0 (h k) n :=
      first_entry_optimal hβ subset_rfl hinv (Nat.find_spec (hreach (h k)) |> fun h' => by
        rwa [hfind] at h') (fun t ht => by
          have := Nat.find_min (hreach (h k)) (show t < Nat.find (hreach (h k)) by omega)
          exact this) 0
    simp only [cutPayoff, pow_zero, Function.iterate_zero, id_eq, add_zero, one_mul] at hge
    rw [max_eq_right]
    have := mul_le_mul_of_nonneg_left hge hβ.le
    simp only [cutPayoff, add_zero] at this ⊢
    linarith

/-- **Exercise 5.5a.** `treeValue` is the largest payoff from any cutting time. -/
theorem le_treeValue (hβ : 0 < β) (hinv : MapsTo h (stopSet h β 0) (stopSet h β 0))
    (hreach : ∀ k, ∃ t, h^[t] k ∈ stopSet h β 0) (k : ℝ) (T : ℕ) :
    β ^ T * h^[T] k ≤ treeValue h β hreach k := by
  classical
  have := first_entry_optimal hβ subset_rfl hinv (Nat.find_spec (hreach k))
    (fun t ht => Nat.find_min (hreach k) ht) T
  simpa [cutPayoff, treeValue] using this

/-! ### Exercise 5.5b: replanting -/

/-- The land value of the stationary rotation of length `T` from a sapling of size `s`:
`L(T) = (βᵀk_T − c)/(1 − βᵀ)` (Faustmann). -/
noncomputable def rotationValue (h : ℝ → ℝ) (β c s : ℝ) (T : ℕ) : ℝ :=
  (β ^ T * h^[T] s - c) / (1 - β ^ T)

/-- `L(T)` is the value of planting, cutting at `T` and starting again:
`L(T) = βᵀ(k_T + L(T)) − c`. -/
theorem faustmann_identity (hβ0 : 0 < β) (hβ1 : β < 1) (c s : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    rotationValue h β c s T = cutPayoff h β (rotationValue h β c s T) s T - c := by
  have hlt : β ^ T < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have hne : 1 - β ^ T ≠ 0 := by linarith
  simp only [rotationValue, cutPayoff]
  field_simp
  ring

/-- **Exercise 5.5b.** If `T*` is a best rotation, `L* = L(T*)` solves the land-value equation
`L = max_{T ≥ 1} βᵀ(k_T + L) − c`. -/
theorem faustmann_fe (hβ0 : 0 < β) (hβ1 : β < 1) (c s : ℝ) {Tstar : ℕ} (hTs : 1 ≤ Tstar)
    (hbest : ∀ T, 1 ≤ T → rotationValue h β c s T ≤ rotationValue h β c s Tstar) :
    (∀ T, 1 ≤ T → cutPayoff h β (rotationValue h β c s Tstar) s T - c ≤
      rotationValue h β c s Tstar) ∧
    cutPayoff h β (rotationValue h β c s Tstar) s Tstar - c = rotationValue h β c s Tstar := by
  refine ⟨fun T hT => ?_, (faustmann_identity hβ0 hβ1 c s hTs).symm⟩
  have hlt : β ^ T < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have hb := hbest T hT
  simp only [rotationValue] at hb
  rw [div_le_iff₀ (by linarith)] at hb
  have hb' : β ^ T * h^[T] s - c ≤ rotationValue h β c s Tstar * (1 - β ^ T) := hb
  simp only [cutPayoff]
  linarith

/-- If trees grow and the gain from waiting `βh(k) − k` falls with size past `k₁`, then the
part of `S_L` beyond `k₁` is `h`-invariant. -/
theorem antitone_invariant {k₁ : ℝ} (hgrow : ∀ k, k ≤ h k)
    (hanti : AntitoneOn (fun k => β * h k - k) (Ici k₁)) :
    MapsTo h (stopSet h β L ∩ Ici k₁) (stopSet h β L ∩ Ici k₁) := by
  rintro k ⟨hk, hk₁⟩
  have hk₁' : h k ∈ Ici k₁ := mem_Ici.2 ((mem_Ici.1 hk₁).trans (hgrow k))
  refine ⟨?_, hk₁'⟩
  exact (hanti hk₁ hk₁' (hgrow k)).trans hk

/-- **Exercise 5.5b.** Let `L*` be the best rotation value. Starting from a sapling `s`, cut at
the first `T_e ≥ 1` with `βh(k_T) − k_T ≤ (1 − β)L*`. If the path stays in that set beyond
`k₁`, the rotation of length `T_e` is optimal: `L(T_e) = L*`. -/
theorem ex_5_5b (hβ0 : 0 < β) (hβ1 : β < 1) (c s : ℝ) {k₁ : ℝ} (hgrow : ∀ k, k ≤ h k)
    {Tstar : ℕ} (hTs : 1 ≤ Tstar)
    (hbest : ∀ T, 1 ≤ T → rotationValue h β c s T ≤ rotationValue h β c s Tstar)
    (hanti : AntitoneOn (fun k => β * h k - k) (Ici k₁)) {Te : ℕ} (hTe : 1 ≤ Te)
    (hin : h^[Te] s ∈ stopSet h β (rotationValue h β c s Tstar) ∩ Ici k₁)
    (hbefore : ∀ t < Te, h^[t] s ∉ stopSet h β (rotationValue h β c s Tstar)) :
    rotationValue h β c s Te = rotationValue h β c s Tstar := by
  set Ls := rotationValue h β c s Tstar
  obtain ⟨hfe, hfeq⟩ := faustmann_fe hβ0 hβ1 c s hTs hbest
  have hopt := first_entry_optimal hβ0 inter_subset_left (antitone_invariant hgrow hanti) hin
    hbefore Tstar
  have hle := hfe Te hTe
  -- so `βᵀᵉ(k_{Tₑ} + L*) − c = L*`, and `L*` solves the rotation identity at `Tₑ`
  have heq : cutPayoff h β Ls s Te - c = Ls := by linarith
  have hlt : β ^ Te < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  simp only [cutPayoff] at heq
  simp only [rotationValue]
  rw [div_eq_iff (by linarith)]
  linarith

end StokeyLucasPrescott.DeterministicApplications

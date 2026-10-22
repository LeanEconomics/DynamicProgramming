/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.Atoms
import Mathlib.Data.ZMod.Basic

/-!
# Periods and cycles on a countable space (MT §5.4.1–5.4.2, Lemma D.7.4)

Meyn and Tweedie, §5.4.1–5.4.2, pp. 110–112, and Lemma D.7.4 of the appendix, which §5.4 uses.

**The g.c.d. of a set of times.**
* `setGcd S`: the greatest common divisor of `S ⊆ ℕ`, the largest common divisor of its
  elements. For an additively closed `S` with a positive element (`IsAddClosed`):
  `setGcd_dvd` (it divides every element), `dvd_setGcd` (every common divisor divides it),
  `setGcd_pos`, and **Lemma D.7.4** (`lemma_D_7_4`): `S` contains all large multiples of
  `setGcd S`. The proof uses the least positive difference of two elements of `S ∪ {0}`, which is
  the g.c.d. (`exists_gcd_witness`); no Bézout identity is needed.

**Countable spaces** (measurable singletons).
* `returnSet P α = {n ≥ 1 : Pⁿ(α, α) > 0}`, `periodAt P α = d(α)` (5.37), p. 111;
  `returnSet_isAddClosed`; `periodAt_dvd`: `Pⁿ(α, α) > 0` with `n ≥ 1` implies `d(α) ∣ n`.
* **Proposition 5.4.1** (`proposition_5_4_1`, p. 111): the period is a class property.
* **Proposition 5.4.2** (`proposition_5_4_2`, p. 111): an irreducible chain with period `d` has
  disjoint cyclic classes `D_i`, `i ∈ ZMod d`, covering `X`, with `P(x, D_{i+1}) = 1` on `D_i`
  (5.39).
* `IsAperiodicCountable`, `IsStronglyAperiodicCountable` (p. 112);
  `IsStronglyAperiodicCountable.isAperiodic`: strong aperiodicity implies aperiodicity.
* **Proposition 5.4.3** (`proposition_5_4_3`, p. 112): for `Pᵈ`, each cyclic class is absorbing
  and irreducible, and every state has period `1` for `Pᵈ`.
* `cycleChain`, `cycleChain_pow_self` (p. 110): the deterministic cycle `x ↦ x + 1` on
  `Fin (d + 1)` has `Pⁿ(x, x) > 0` iff `d + 1 ∣ n`, so every state has period `d + 1`.

**Corrections.** None.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### The g.c.d. of an additively closed set of times -/

/-- `S ⊆ ℕ` is closed under addition. -/
def IsAddClosed (S : Set ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S

/-- The **greatest common divisor** of `S ⊆ ℕ`: the largest common divisor of its elements
(as used in (5.37) and (5.40)). -/
noncomputable def setGcd (S : Set ℕ) : ℕ := sSup {d | ∀ s ∈ S, d ∣ s}

/-- Multiples `(q + 1) b` of an element of an additively closed set lie in it. -/
theorem IsAddClosed.succ_mul_mem {S : Set ℕ} (hS : IsAddClosed S) {b : ℕ} (hb : b ∈ S) (q : ℕ) :
    (q + 1) * b ∈ S := by
  induction q with
  | zero => simpa using hb
  | succ q ih => rw [add_mul, one_mul]; exact hS _ ih _ hb

/-- Multiples `q b` of an element of `S ∪ {0}` lie in `S ∪ {0}`. -/
theorem IsAddClosed.mul_mem_zero {S : Set ℕ} (hS : IsAddClosed S) {b : ℕ} (hb : b = 0 ∨ b ∈ S)
    (q : ℕ) : q * b = 0 ∨ q * b ∈ S := by
  rcases hb with rfl | hb
  · left; simp
  · rcases q with _ | q
    · left; simp
    · exact Or.inr (hS.succ_mul_mem hb q)

/-- The sum of an element of `S ∪ {0}` and an element of `S` lies in `S`. -/
theorem IsAddClosed.add_mem_of_zero {S : Set ℕ} (hS : IsAddClosed S) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
  rcases ha with rfl | ha
  · simpa using hb
  · exact hS _ ha _ hb

/-- **The g.c.d. as a least difference.** If `S` is additively closed and has a positive element,
the least positive difference `g = b − a` of elements of `S ∪ {0}` (with `b ∈ S`) divides every
element of `S`, and every common divisor of `S` divides it. -/
theorem exists_gcd_witness {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
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

/-- For an additively closed `S` with a positive element, `setGcd S` is the least positive
difference of `exists_gcd_witness`. -/
theorem setGcd_spec {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ a, 0 < setGcd S ∧ (a = 0 ∨ a ∈ S) ∧ a + setGcd S ∈ S ∧ (∀ s ∈ S, setGcd S ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ setGcd S := by
  obtain ⟨g, a, hg, ha, hag, hdvd, hmax⟩ := exists_gcd_witness hS hs₀ hpos
  have heq : setGcd S = g := by
    refine IsGreatest.csSup_eq ⟨hdvd, fun d hd => Nat.le_of_dvd hg (hmax d hd)⟩
  rw [heq]
  exact ⟨a, hg, ha, hag, hdvd, hmax⟩

/-- `setGcd S` divides every element of `S`. -/
theorem setGcd_dvd {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {s : ℕ} (hs : s ∈ S) : setGcd S ∣ s := by
  obtain ⟨a, -, -, -, h, -⟩ := setGcd_spec hS hs₀ hpos
  exact h s hs

/-- Every common divisor of `S` divides `setGcd S`. -/
theorem dvd_setGcd {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {d : ℕ} (hd : ∀ s ∈ S, d ∣ s) : d ∣ setGcd S := by
  obtain ⟨a, -, -, -, -, h⟩ := setGcd_spec hS hs₀ hpos
  exact h d hd

/-- `setGcd S > 0`. -/
theorem setGcd_pos {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    0 < setGcd S := by
  obtain ⟨a, h, -⟩ := setGcd_spec hS hs₀ hpos
  exact h

/-- **Lemma D.7.4** (MT p. 549, used in §5.4): an additively closed set of naturals with a positive
element contains every large enough multiple of its g.c.d. -/
theorem lemma_D_7_4 {S : Set ℕ} (hS : IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ N, ∀ n ≥ N, n * setGcd S ∈ S := by
  obtain ⟨a, hg, ha, hag, hdvd, -⟩ := setGcd_spec hS hs₀ hpos
  set g := setGcd S
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

/-! ### The period of a state on a countable space -/

variable {X : Type*} [MeasurableSpace X]

/-- The return times `{n ≥ 1 : Pⁿ(α, α) > 0}` of a state `α`. -/
def returnSet (P : Kernel X X) (α : X) : Set ℕ := {n | 0 < n ∧ 0 < (P ^ n) α {α}}

/-- The **period** `d(α) = g.c.d.{n ≥ 1 : Pⁿ(α, α) > 0}` of a state (5.37), MT p. 111. -/
noncomputable def periodAt (P : Kernel X X) (α : X) : ℕ := setGcd (returnSet P α)

/-- A chain that moves from `D i` into `D (i + 1)` with probability one moves from `D i` into
`D (i + n)` in `n` steps with probability one. -/
theorem pow_apply_eq_one_of_step (P : Kernel X X) [IsMarkovKernel P] {d : ℕ}
    {D : ZMod d → Set X} (hD : ∀ i, MeasurableSet (D i))
    (hstep : ∀ i, ∀ x ∈ D i, P x (D (i + 1)) = 1) (n : ℕ) :
    ∀ i, ∀ x ∈ D i, (P ^ n) x (D (i + n)) = 1 := by
  induction n with
  | zero =>
    intro i x hx
    rw [pow_zero_apply, Nat.cast_zero, add_zero, Measure.dirac_apply' _ (hD i),
      indicator_of_mem hx, Pi.one_apply]
  | succ n ih =>
    intro i x hx
    have := isMarkovKernel_pow P n
    have := isMarkovKernel_pow P (n + 1)
    refine le_antisymm prob_le_one ?_
    rw [pow_succ_apply' P n x (hD _)]
    calc (1 : ℝ≥0∞) = (P ^ n) x (D (i + n)) := (ih i x hx).symm
      _ = ∫⁻ y in D (i + n), 1 ∂(P ^ n) x := by rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ y in D (i + n), P y (D (i + ↑(n + 1))) ∂(P ^ n) x := by
          refine setLIntegral_mono (Kernel.measurable_coe _ (hD _)) fun y hy => ?_
          rw [Nat.cast_succ, ← add_assoc, hstep _ y hy]
      _ ≤ ∫⁻ y, P y (D (i + ↑(n + 1))) ∂(P ^ n) x := setLIntegral_le_lintegral _ _

variable [MeasurableSingletonClass X]

/-- The return times are closed under addition: `P^{m+n}(α, α) ≥ Pᵐ(α, α) Pⁿ(α, α)`. -/
theorem returnSet_isAddClosed (P : Kernel X X) (α : X) : IsAddClosed (returnSet P α) :=
  fun m hm n hn => ⟨Nat.add_pos_left hm.1 n,
    (ENNReal.mul_pos hm.2.ne' hn.2.ne').trans_le (pow_add_singleton_ge P m n α α α)⟩

/-- MT p. 111: `Pⁿ(α, α) = 0` unless `d(α)` divides `n` (for `n ≥ 1`). -/
theorem periodAt_dvd (P : Kernel X X) {α : X} {n : ℕ} (hn : n ∈ returnSet P α) :
    periodAt P α ∣ n :=
  setGcd_dvd (returnSet_isAddClosed P α) hn hn.1 hn

/-- If `α ↔ y` with `α ≠ y`, there are `m, n ≥ 1` with `Pᵐ(α, y) > 0` and `Pⁿ(y, α) > 0`. -/
theorem exists_pow_pos_of_communicates (P : Kernel X X) [IsMarkovKernel P] {α y : X}
    (h : Communicates P α y) (hne : α ≠ y) :
    ∃ m n, 0 < m ∧ 0 < n ∧ 0 < (P ^ m) α {y} ∧ 0 < (P ^ n) y {α} := by
  obtain ⟨m, hm⟩ := (hitProb_pos_iff P (measurableSet_singleton y) α).1 (h.1.resolve_left hne)
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P (measurableSet_singleton α) y).1
    (h.2.resolve_left (Ne.symm hne))
  exact ⟨m + 1, n + 1, by omega, by omega, hm, hn⟩

/-- Every return time of `y` is a return time of `α` minus a fixed return time, when
`α ↔ y`: `d(α)` divides every return time of `y`. -/
theorem periodAt_dvd_of_communicates (P : Kernel X X) [IsMarkovKernel P] {α y : X}
    (h : Communicates P α y) {k : ℕ} (hk : k ∈ returnSet P y) : periodAt P α ∣ k := by
  by_cases hne : α = y
  · subst hne; exact periodAt_dvd P hk
  obtain ⟨m, n, hm0, hn0, hm, hn⟩ := exists_pow_pos_of_communicates P h hne
  have h1 : m + n ∈ returnSet P α :=
    ⟨by omega, (ENNReal.mul_pos hm.ne' hn.ne').trans_le (pow_add_singleton_ge P m n α y α)⟩
  have h2 : m + k + n ∈ returnSet P α := by
    refine ⟨by omega, ?_⟩
    have h3 := (ENNReal.mul_pos hm.ne' hk.2.ne').trans_le (pow_add_singleton_ge P m k α y y)
    exact (ENNReal.mul_pos h3.ne' hn.ne').trans_le (pow_add_singleton_ge P (m + k) n α y α)
  have := periodAt_dvd P h2
  rw [show m + k + n = k + (m + n) by omega] at this
  exact (Nat.dvd_add_left (periodAt_dvd P h1)).1 this

/-- **Proposition 5.4.1** (MT p. 111): if `y ∈ C(α)` then `d(α) = d(y)`. -/
theorem proposition_5_4_1 (P : Kernel X X) [IsMarkovKernel P] {α y : X}
    (h : y ∈ commClass P α) : periodAt P α = periodAt P y := by
  by_cases hne : α = y
  · rw [hne]
  obtain ⟨m, n, hm0, hn0, hm, hn⟩ := exists_pow_pos_of_communicates P h hne
  have hα : m + n ∈ returnSet P α :=
    ⟨by omega, (ENNReal.mul_pos hm.ne' hn.ne').trans_le (pow_add_singleton_ge P m n α y α)⟩
  have hy : n + m ∈ returnSet P y :=
    ⟨by omega, (ENNReal.mul_pos hn.ne' hm.ne').trans_le (pow_add_singleton_ge P n m y α y)⟩
  refine Nat.dvd_antisymm ?_ ?_
  · exact dvd_setGcd (returnSet_isAddClosed P y) hy hy.1
      fun k hk => periodAt_dvd_of_communicates P h hk
  · exact dvd_setGcd (returnSet_isAddClosed P α) hα hα.1
      fun k hk => periodAt_dvd_of_communicates P ((proposition_4_1_1 P).symm h) hk

variable [Countable X]

/-- An irreducible chain on a nonempty space returns to every state: for every `y` there is
`M ≥ 1` with `Pᴹ(y, α) > 0`. -/
theorem exists_return_pow_pos (P : Kernel X X) [IsMarkovKernel P] [Nonempty X]
    (hP : IsIrreducibleChain P) (y α : X) : ∃ M, 0 < M ∧ 0 < (P ^ M) y {α} := by
  have hc : ∀ x, ∃ M, 0 < (P ^ (M + 1)) x {α} := fun x => by
    rcases ((isIrreducibleChain_iff P).1 hP x α).1 with h | h
    · subst h
      -- the chain leaves `α` to some state, which leads back to `α`
      have h1 : 0 < P x univ := by simp
      have hsum : ∃ z, 0 < (P ^ 1) x {z} := by
        rw [pow_one]
        by_contra hz
        push Not at hz
        have : P x univ = 0 := by
          rw [← iUnion_of_singleton (α := X)]
          exact measure_iUnion_null_iff.2 fun z => nonpos_iff_eq_zero.1 (hz z)
        exact h1.ne' this
      obtain ⟨z, hz⟩ := hsum
      obtain ⟨n, hn⟩ := (leads_iff_exists_pow P z x).1 ((isIrreducibleChain_iff P).1 hP z x).1
      exact ⟨n, by
        have := (ENNReal.mul_pos hz.ne' hn.ne').trans_le (pow_add_singleton_ge P 1 n x z x)
        rwa [add_comm] at this⟩
    · exact (hitProb_pos_iff P (measurableSet_singleton α) x).1 h
  obtain ⟨M, hM⟩ := hc y
  exact ⟨M + 1, by omega, hM⟩

omit [MeasurableSingletonClass X] [Countable X] in
/-- The cyclic class of `y` relative to a base state `α`: the class mod `d` of the times `k` with
`Pᵏ(α, y) > 0`. -/
def cyclicClass (P : Kernel X X) (α : X) (d : ℕ) (i : ZMod d) : Set X :=
  {y | ∃ k : ℕ, (k : ZMod d) = i ∧ 0 < (P ^ k) α {y}}

/-- **Proposition 5.4.2** (MT p. 111). Let `Φ` be an irreducible chain on a countable space and
`d = d(α)` the common period. The cyclic classes `D_i`, `i ∈ ZMod d`, are disjoint, cover `X`,
and `P(x, D_{i+1}) = 1` for `x ∈ D_i` (5.39). -/
theorem proposition_5_4_2 (P : Kernel X X) [IsMarkovKernel P] [Nonempty X]
    (hP : IsIrreducibleChain P) (α : X) :
    (∀ i j : ZMod (periodAt P α), i ≠ j →
        Disjoint (cyclicClass P α (periodAt P α) i) (cyclicClass P α (periodAt P α) j)) ∧
      (⋃ i, cyclicClass P α (periodAt P α) i) = univ ∧
      ∀ i, ∀ x ∈ cyclicClass P α (periodAt P α) i,
        P x (cyclicClass P α (periodAt P α) (i + 1)) = 1 := by
  set d := periodAt P α
  refine ⟨fun i j hij => Set.disjoint_left.2 fun y hi hj => hij ?_, ?_, fun i x hx => ?_⟩
  · obtain ⟨k, rfl, hk⟩ := hi
    obtain ⟨k', rfl, hk'⟩ := hj
    obtain ⟨M, hM0, hM⟩ := exists_return_pow_pos P hP y α
    have h1 : k + M ∈ returnSet P α :=
      ⟨by omega, (ENNReal.mul_pos hk.ne' hM.ne').trans_le (pow_add_singleton_ge P k M α y α)⟩
    have h2 : k' + M ∈ returnSet P α :=
      ⟨by omega, (ENNReal.mul_pos hk'.ne' hM.ne').trans_le (pow_add_singleton_ge P k' M α y α)⟩
    have e1 := (ZMod.natCast_eq_zero_iff _ _).2 (periodAt_dvd P h1)
    have e2 := (ZMod.natCast_eq_zero_iff _ _).2 (periodAt_dvd P h2)
    push_cast at e1 e2
    exact add_right_cancel (e1.trans e2.symm)
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := (leads_iff_exists_pow P α y).1 ((isIrreducibleChain_iff P).1 hP α y).1
    exact ⟨k, k, rfl, hk⟩
  · obtain ⟨k, rfl, hk⟩ := hx
    have hzero : P x (cyclicClass P α d ((k : ZMod d) + 1))ᶜ = 0 := by
      by_contra hne
      obtain ⟨y, hy, hpos⟩ := exists_singleton_pos_of_pos (P x) (pos_iff_ne_zero.2 hne)
      refine hy ⟨k + 1, by push_cast; rfl, ?_⟩
      have := (ENNReal.mul_pos hk.ne' (by rw [pow_one]; exact hpos.ne')).trans_le
        (pow_add_singleton_ge P k 1 α x y)
      exact this
    rw [prob_compl_eq_zero_iff (measurableSet_of_countable _)] at hzero
    exact hzero

/-- An irreducible chain on a countable space is **aperiodic** if `d(x) = 1` for every `x`
(MT p. 112). -/
def IsAperiodicCountable (P : Kernel X X) : Prop := ∀ x, periodAt P x = 1

/-- An irreducible chain on a countable space is **strongly aperiodic** if `P(x, x) > 0` for some
`x` (MT p. 112). -/
def IsStronglyAperiodicCountable (P : Kernel X X) : Prop := ∃ x, 0 < P x {x}

omit [Countable X] in
/-- A strongly aperiodic irreducible chain is aperiodic: `1` is a return time, so the common
period is `1`. -/
theorem IsStronglyAperiodicCountable.isAperiodic {P : Kernel X X} [IsMarkovKernel P]
    [Nonempty X] (hP : IsIrreducibleChain P) (h : IsStronglyAperiodicCountable P) :
    IsAperiodicCountable P := by
  obtain ⟨x, hx⟩ := h
  intro y
  have h1 : 1 ∈ returnSet P x := ⟨one_pos, by rwa [pow_one]⟩
  rw [← proposition_5_4_1 P (((isIrreducibleChain_iff P).1 hP) x y)]
  exact Nat.dvd_one.1 (periodAt_dvd P h1)

/-- **Proposition 5.4.3** (MT p. 112). Let `Φ` be irreducible on a countable space, with period
`d` and cyclic classes `D_i`. For the chain `Φ_d` with transition matrix `Pᵈ`: each `D_i` is
absorbing, any two states of `D_i` communicate under `Pᵈ`, and every state has period `1` under
`Pᵈ`. -/
theorem proposition_5_4_3 (P : Kernel X X) [IsMarkovKernel P] [Nonempty X]
    (hP : IsIrreducibleChain P) (α : X) :
    (∀ i, ∀ x ∈ cyclicClass P α (periodAt P α) i,
        (P ^ periodAt P α) x (cyclicClass P α (periodAt P α) i) = 1) ∧
      (∀ i, ∀ x ∈ cyclicClass P α (periodAt P α) i, ∀ y ∈ cyclicClass P α (periodAt P α) i,
        ∃ q, 0 < ((P ^ periodAt P α) ^ q) x {y}) ∧
      ∀ x, periodAt (P ^ periodAt P α) x = 1 := by
  set d := periodAt P α with hd
  obtain ⟨hdisj, -, hstep⟩ := proposition_5_4_2 P hP α
  have hmeas : ∀ i, MeasurableSet (cyclicClass P α d i) := fun i => measurableSet_of_countable _
  have hpow := pow_apply_eq_one_of_step P hmeas hstep
  have hperiod : ∀ x, periodAt P x = d := fun x =>
    (proposition_5_4_1 P (((isIrreducibleChain_iff P).1 hP) α x)).symm
  refine ⟨fun i x hx => ?_, fun i x hx y hy => ?_, fun x => ?_⟩
  · have := hpow d i x hx
    rwa [ZMod.natCast_self, add_zero] at this
  · obtain ⟨k, hk⟩ := (leads_iff_exists_pow P x y).1 (((isIrreducibleChain_iff P).1 hP) x y).1
    -- `y ∈ D_{i+k}`, hence `d ∣ k`
    have hyk : y ∈ cyclicClass P α d (i + k) := by
      have := isMarkovKernel_pow P k
      by_contra hc
      have h1 := hpow k i x hx
      rw [← prob_compl_eq_zero_iff (hmeas _)] at h1
      exact hk.ne' (measure_mono_null (singleton_subset_iff.2 hc) h1)
    have hik : i + k = i := by
      by_contra hne
      exact Set.disjoint_left.1 (hdisj _ _ hne) hyk hy
    have hdk : d ∣ k := (ZMod.natCast_eq_zero_iff k d).1 (by
      have := congrArg (fun z => z - i) hik
      simpa using this)
    obtain ⟨q, rfl⟩ := hdk
    exact ⟨q, by rwa [← pow_mul]⟩
  · have hd0 : 0 < d := by
      obtain ⟨M, hM0, hM⟩ := exists_return_pow_pos P hP α α
      exact setGcd_pos (returnSet_isAddClosed P α) ⟨hM0, hM⟩ hM0
    -- a return time of `x` for `Pᵈ`
    obtain ⟨M, hM0, hM⟩ := exists_return_pow_pos P hP x x
    have hMr : M ∈ returnSet P x := ⟨hM0, hM⟩
    obtain ⟨q₀, hq₀⟩ := hperiod x ▸ periodAt_dvd P hMr
    have hq₀r : q₀ ∈ returnSet (P ^ d) x := by
      refine ⟨Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq₀; omega, ?_⟩
      rw [← pow_mul, ← hq₀]; exact hM
    -- `d · d'(x)` divides every return time of `x`
    have hdvd : d * periodAt (P ^ d) x ∣ periodAt P x := by
      refine dvd_setGcd (returnSet_isAddClosed P x) hMr hM0 fun n hn => ?_
      obtain ⟨q, rfl⟩ := hperiod x ▸ periodAt_dvd P hn
      have hq : q ∈ returnSet (P ^ d) x :=
        ⟨Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hn; exact lt_irrefl _ hn.1,
          by rw [← pow_mul]; exact hn.2⟩
      exact Nat.mul_dvd_mul_left d (periodAt_dvd (P ^ d) hq)
    rw [hperiod x] at hdvd
    have h1 : d * periodAt (P ^ d) x ∣ d * 1 := by rwa [mul_one]
    exact Nat.dvd_one.1 ((Nat.mul_dvd_mul_iff_left hd0).1 h1)

/-! ### The deterministic cycle (MT p. 110) -/

/-- The deterministic cycle `x ↦ x + 1` on `{0, …, d}` (MT p. 110). -/
noncomputable def cycleChain (d : ℕ) : Kernel (Fin (d + 1)) (Fin (d + 1)) :=
  Kernel.deterministic (fun x => x + 1) (measurable_of_countable _)

open Fin.NatCast in
/-- The `n`-step kernel of the cycle is the shift by `n`. -/
theorem cycleChain_pow (d n : ℕ) :
    cycleChain d ^ n = Kernel.deterministic (fun x => x + (n : Fin (d + 1)))
      (measurable_of_countable _) := by
  induction n with
  | zero =>
    ext1 x
    rw [pow_zero]
    change Kernel.id x = _
    simp [Kernel.id, Kernel.deterministic_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    change Kernel.deterministic _ _ ∘ₖ Kernel.deterministic _ _ = _
    rw [Kernel.deterministic_comp_deterministic]
    congr 1
    ext1 x
    simp only [Function.comp, Nat.cast_succ]
    abel

open Fin.NatCast in
/-- MT p. 110: in the deterministic cycle, `Pⁿ(x, x) > 0` iff `n` is a multiple of `d + 1`. -/
theorem cycleChain_pow_self (d n : ℕ) (x : Fin (d + 1)) :
    0 < (cycleChain d ^ n) x {x} ↔ (d + 1) ∣ n := by
  rw [cycleChain_pow, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton x)]
  have : (x + (n : Fin (d + 1)) ∈ ({x} : Set (Fin (d + 1)))) ↔ (d + 1) ∣ n := by
    rw [mem_singleton_iff, add_eq_left, Fin.natCast_eq_zero]
  by_cases h : (d + 1) ∣ n
  · rw [indicator_of_mem (this.2 h)]; simp [h]
  · rw [indicator_of_notMem (fun h' => h (this.1 h'))]; simp [h]

/-- Every state of the deterministic cycle on `d + 1` points has period `d + 1` (MT p. 110). -/
theorem periodAt_cycleChain (d : ℕ) (x : Fin (d + 1)) : periodAt (cycleChain d) x = d + 1 := by
  have hmem : d + 1 ∈ returnSet (cycleChain d) x :=
    ⟨by omega, (cycleChain_pow_self d _ x).2 dvd_rfl⟩
  have hS := returnSet_isAddClosed (cycleChain d) x
  refine Nat.dvd_antisymm (periodAt_dvd _ hmem) (dvd_setGcd hS hmem (by omega) fun n hn => ?_)
  exact (cycleChain_pow_self d n x).1 hn.2

end MeynTweedie.FErgodicity

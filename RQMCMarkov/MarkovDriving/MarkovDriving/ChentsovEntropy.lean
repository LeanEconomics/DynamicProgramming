/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # An entropy lemma: a stationary chain driven by i.i.d. inputs is independent of them

The general (coupling-free) Chentsov theorem (`ChentsovGeneral`) reduces to a statement about
finite distributions. Let `X` and `C` be finite, `F : X → C → X`, and `c` a law on `C`. Suppose
`q m` is a joint law of `(X₀, Z₀, …, Z_{m-1})` for every `m`, with `Z₀, …, Z_{m-1}` i.i.d. `c`,
with consistent marginals, and **stationary** for `X_{t+1} = F X_t Z_t`: the law of
`(X₁, Z₁, …, Z_m)` is again `q m`. No independence of `X₀` from the `Z`'s is assumed (in the
application `X₀` may depend on the "future" inputs). Then `X₀` **is** independent of `Z₀`
(`chentsov_entropy_core`), so its law `ρ` is stationary for the Markov matrix
`P x j = c {a : F x a = j}` (`chentsov_entropy_stationary`).

**Proof (information theory).** Let `I m` be the mutual information of `X₀` and
`(Z₀, …, Z_{m-1})`. Data processing for the map `(X₀, Z₀) ↦ X₁ = F X₀ Z₀`, stationarity, and
the chain rule (with `Z₀` independent of `(Z₁, …)`) give `I (m+1) ≥ I m + I 1`, so
`I m ≥ m · I 1`; but `I m ≤ H(X₀) < ∞`. Hence `I 1 = 0`, i.e. `X₀` and `Z₀` are independent
(Gibbs' inequality with its equality case). The entropy is finite because `X` is finite; this is
where the finite state space is used.

**Results.**
* `sub_le_mul_log_div`, `sub_lt_mul_log_div`: `a - b ≤ a log (a/b)`, strictly unless `a = b`.
* `eq_of_klSum_le`: Gibbs' inequality, equality case.
* `logSum_le`: the log-sum inequality; `klSum_pushSum_le`: data processing for the
  Kullback–Leibler sum `klSum p q = ∑ p log (p/q)` under a map.
* `chentsov_entropy_core`, `chentsov_entropy_stationary`.
-/

namespace RQMCMarkov.MarkovDriving

open Finset Real

/-- The Kullback–Leibler sum `∑ₓ p x log (p x / q x)` (with `log 0 = 0`). -/
noncomputable def klSum {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- **Per-term Gibbs inequality:** `a - b ≤ a log (a/b)` for `a, b ≥ 0` with `b = 0 → a = 0`. -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h0 | hapos
  · rw [← h0, zero_mul]
    linarith
  have hbpos : 0 < b := lt_of_le_of_ne hb fun h => hapos.ne' (hab h.symm)
  have hl := Real.log_le_sub_one_of_pos (div_pos hbpos hapos)
  have hinv : a / b = (b / a)⁻¹ := (inv_div b a).symm
  rw [hinv, Real.log_inv]
  have : a * (b / a) = b := mul_div_cancel₀ b hapos.ne'
  nlinarith

/-- **Strict per-term Gibbs inequality:** `a - b < a log (a/b)` when moreover `a ≠ b`. -/
theorem sub_lt_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0)
    (hne : a ≠ b) : a - b < a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h0 | hapos
  · rw [← h0, zero_mul]
    have : 0 < b := lt_of_le_of_ne hb (fun h => hne (h0.symm.trans h))
    linarith
  have hbpos : 0 < b := lt_of_le_of_ne hb fun h => hapos.ne' (hab h.symm)
  have hne' : b / a ≠ 1 := fun h => hne ((div_eq_one_iff_eq hapos.ne').1 h).symm
  have hl := Real.log_lt_sub_one_of_pos (div_pos hbpos hapos) hne'
  have hinv : a / b = (b / a)⁻¹ := (inv_div b a).symm
  rw [hinv, Real.log_inv]
  have : a * (b / a) = b := mul_div_cancel₀ b hapos.ne'
  nlinarith

/-- **Gibbs' inequality:** `∑ p - ∑ q ≤ klSum p q`. -/
theorem sum_sub_sum_le_klSum {α : Type*} [Fintype α] {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hpq : ∀ x, q x = 0 → p x = 0) : ∑ x, p x - ∑ x, q x ≤ klSum p q := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => sub_le_mul_log_div (hp x) (hq x) (hpq x)

/-- **Gibbs' inequality, equality case:** if `∑ p = ∑ q` and `klSum p q ≤ 0` then `p = q`. -/
theorem eq_of_klSum_le {α : Type*} [Fintype α] {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hpq : ∀ x, q x = 0 → p x = 0) (hsum : ∑ x, p x = ∑ x, q x)
    (hkl : klSum p q ≤ 0) : p = q := by
  funext x
  by_contra hne
  have hlt : ∑ y, (p y - q y) < klSum p q := by
    unfold klSum
    exact Finset.sum_lt_sum (fun y _ => sub_le_mul_log_div (hp y) (hq y) (hpq y))
      ⟨x, Finset.mem_univ x, sub_lt_mul_log_div (hp x) (hq x) (hpq x) hne⟩
  rw [Finset.sum_sub_distrib, hsum, sub_self] at hlt
  linarith

/-- **The log-sum inequality:** `(∑ a) log (∑ a / ∑ b) ≤ ∑ a log (a/b)` for `a, b ≥ 0` with
`b = 0 → a = 0`. -/
theorem logSum_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  rcases hA0.eq_or_lt with hA0' | hApos
  · have hai : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ha i).1 hA0'.symm
    rw [← hA0', zero_mul, Finset.sum_eq_zero fun i hi => by rw [hai i hi, zero_mul]]
  have hBpos : 0 < B := by
    rcases (Finset.sum_nonneg fun i (_ : i ∈ s) => hb i).eq_or_lt with h | h
    · have hbi : ∀ i ∈ s, b i = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hb i).1 h.symm
      have : A = 0 := Finset.sum_eq_zero fun i hi => hab i (hbi i hi)
      linarith
    · exact h
  set κ := A / B with hκ
  have hκpos : 0 < κ := div_pos hApos hBpos
  have hterm : ∀ i ∈ s, a i - b i * κ ≤ a i * Real.log (a i / b i) - a i * Real.log κ := by
    intro i _
    have h := sub_le_mul_log_div (ha i) (mul_nonneg (hb i) hκpos.le) fun h0 =>
      hab i ((mul_eq_zero.1 h0).resolve_right hκpos.ne')
    rcases (ha i).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_mul, sub_zero]
      rw [← h0] at h
      linarith
    · have hbpos : 0 < b i := lt_of_le_of_ne (hb i) fun h' => hpos.ne' (hab i h'.symm)
      have hlog : Real.log (a i / (b i * κ)) = Real.log (a i / b i) - Real.log κ := by
        rw [← div_div, Real.log_div (div_pos hpos hbpos).ne' hκpos.ne']
      rw [hlog, mul_sub] at h
      exact h
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  rw [← hA, ← hB, hκ, mul_div_cancel₀ A hBpos.ne', sub_self] at hsum
  linarith

/-- The push-forward of a function `p : α → ℝ` along `φ : α → β`: fibre sums. -/
noncomputable def pushSum {α β : Type*} [Fintype α] [DecidableEq β] (φ : α → β) (p : α → ℝ)
    (y : β) : ℝ :=
  ∑ x ∈ univ.filter (fun x => φ x = y), p x

/-- **Data processing** for the Kullback–Leibler sum: pushing both arguments forward along a
map can only decrease it. -/
theorem klSum_pushSum_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (φ : α → β)
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hpq : ∀ x, q x = 0 → p x = 0) :
    klSum (pushSum φ p) (pushSum φ q) ≤ klSum p q := by
  unfold klSum
  rw [← Finset.sum_fiberwise Finset.univ φ fun x => p x * Real.log (p x / q x)]
  exact Finset.sum_le_sum fun y _ => logSum_le _ hp hq hpq

/-- Sums over `Fin (L+1) → C` split as a sum over the head and the tail. -/
theorem sum_fin_succ_fun {C : Type*} [Fintype C] {L : ℕ}
    (f : (Fin (L + 1) → C) → ℝ) : ∑ z, f z = ∑ a, ∑ z', f (Fin.cons a z') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => C) _ _ fun _ => rfl).symm

/-- The value of a sum over `Fin 0 → C`. -/
theorem sum_fin_zero_fun {C : Type*} [Fintype C] (f : (Fin 0 → C) → ℝ) :
    ∑ z, f z = f Fin.elim0 := by
  rw [Fintype.sum_unique]
  exact congrArg f (Subsingleton.elim _ _)

variable {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C]

/-- **The entropy core of Chentsov's theorem.** Let `q m x z` be a joint law of `X₀ = x` and the
inputs `(Z₀, …, Z_{m-1}) = z`, whose input marginal is the i.i.d. product of `c`, whose `X₀`
marginal is `ρ` (a probability vector), whose `(X₀, Z₀)` marginal is `r`, and which is
stationary for `X₁ = F X₀ Z₀`. Then `X₀` and `Z₀` are independent: `r x a = ρ x · c a`. -/
theorem chentsov_entropy_core (F : X → C → X) (c : C → ℝ) (ρ : X → ℝ) (r : X → C → ℝ)
    (q : (m : ℕ) → X → (Fin m → C) → ℝ) (hq0 : ∀ m x z, 0 ≤ q m x z)
    (hZ : ∀ m z, ∑ x, q m x z = ∏ k, c (z k)) (hX : ∀ m x, ∑ z, q m x z = ρ x)
    (hr : ∀ L x a, ∑ z', q (L + 1) x (Fin.cons a z') = r x a)
    (hstat : ∀ L j z', ∑ x, ∑ a, (if F x a = j then q (L + 1) x (Fin.cons a z') else 0) =
      q L j z')
    (hρ1 : ∑ x, ρ x = 1) (x : X) (a : C) : r x a = ρ x * c a := by
  classical
  -- basic facts
  have hr0 : ∀ x a, 0 ≤ r x a := fun x a => by
    rw [← hr 0]
    exact Finset.sum_nonneg fun _ _ => hq0 _ _ _
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => by
    rw [← hX 0]
    exact Finset.sum_nonneg fun _ _ => hq0 _ _ _
  have hrX : ∀ x, ∑ a, r x a = ρ x := fun x => by
    rw [← hX 1 x, sum_fin_succ_fun]
    exact Finset.sum_congr rfl fun a _ => (hr 0 x a).symm
  have hrC : ∀ a, ∑ x, r x a = c a := fun a => by
    have h := hZ 1 (Fin.cons a Fin.elim0)
    rw [Fin.prod_univ_one, Fin.cons_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [← hr 0 x a, sum_fin_zero_fun]
  have hc0 : ∀ a, 0 ≤ c a := fun a => by
    rw [← hrC a]
    exact Finset.sum_nonneg fun x _ => hr0 x a
  have hc1 : ∑ a, c a = 1 := by
    simp only [← hrC]
    rw [Finset.sum_comm]
    simp only [hrX]
    exact hρ1
  have hrle : ∀ x a, r x a ≤ ρ x ∧ r x a ≤ c a := fun x a =>
    ⟨(hrX x) ▸ Finset.single_le_sum (fun a _ => hr0 x a) (Finset.mem_univ a),
      (hrC a) ▸ Finset.single_le_sum (fun x _ => hr0 x a) (Finset.mem_univ x)⟩
  have hqle : ∀ m x z, q m x z ≤ ∏ k, c (z k) := fun m x z =>
    (hZ m z) ▸ Finset.single_le_sum (fun x _ => hq0 m x z) (Finset.mem_univ x)
  have hqr : ∀ L x a z', q (L + 1) x (Fin.cons a z') ≤ r x a := fun L x a z' =>
    (hr L x a) ▸ Finset.single_le_sum (fun z _ => hq0 (L + 1) x (Fin.cons a z))
      (Finset.mem_univ z')
  have hpushr : ∀ j, ∑ x, ∑ a, (if F x a = j then r x a else 0) = ρ j := fun j => by
    rw [← hX 0 j, sum_fin_zero_fun, ← hstat 0 j Fin.elim0]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← hr 0 x a, sum_fin_zero_fun]
  -- the mutual informations
  set I : ℕ → ℝ := fun m => ∑ x, ∑ z, q m x z * Real.log (q m x z / (ρ x * ∏ k, c (z k)))
    with hI
  set I1 : ℝ := ∑ x, ∑ a, r x a * Real.log (r x a / (ρ x * c a)) with hI1
  -- `I 0 = 0`
  have hI0 : I 0 = 0 := by
    rw [hI]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [sum_fin_zero_fun, Fin.prod_univ_zero, mul_one]
    have hq00 : q 0 x Fin.elim0 = ρ x := by rw [← hX 0 x, sum_fin_zero_fun]
    rw [hq00]
    rcases (hρ0 x).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · rw [div_self h.ne', Real.log_one, mul_zero]
  -- `I m ≤ H(ρ)`
  have hIle : ∀ m, I m ≤ ∑ x, ρ x * Real.log (1 / ρ x) := by
    intro m
    rw [hI]
    refine Finset.sum_le_sum fun x _ => ?_
    refine (Finset.sum_le_sum fun z _ => ?_).trans_eq
      (by rw [← Finset.sum_mul, hX m x] : ∑ z, q m x z * Real.log (1 / ρ x) = _)
    rcases (hq0 m x z).eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
    · have hcz : 0 < ∏ k, c (z k) := lt_of_lt_of_le h (hqle m x z)
      have hρx : 0 < ρ x := by
        rcases (hρ0 x).eq_or_lt with h' | h'
        · exfalso
          have : q m x z ≤ ρ x := (hX m x) ▸ Finset.single_le_sum (fun z _ => hq0 m x z)
            (Finset.mem_univ z)
          linarith
        · exact h'
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos h (mul_pos hρx hcz)) ?_) h.le
      rw [div_le_div_iff₀ (mul_pos hρx hcz) hρx]
      nlinarith [hqle m x z]
  -- `I 1 ≥ 0`
  have hI1nn : 0 ≤ I1 := by
    have h := sum_sub_sum_le_klSum (α := X × C) (p := fun xa => r xa.1 xa.2)
      (q := fun xa => ρ xa.1 * c xa.2) (fun xa => hr0 _ _)
      (fun xa => mul_nonneg (hρ0 _) (hc0 _)) fun xa h0 => by
        rcases mul_eq_zero.1 h0 with h | h
        · exact le_antisymm (h ▸ (hrle _ _).1) (hr0 _ _)
        · exact le_antisymm (h ▸ (hrle _ _).2) (hr0 _ _)
    unfold klSum at h
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h
    simp only [hrX, ← Finset.mul_sum, hc1, mul_one, hρ1, sub_self] at h
    exact h
  -- superadditivity `I (L+1) ≥ I L + I 1`
  have hsuper : ∀ L, I L + I1 ≤ I (L + 1) := by
    intro L
    -- split each term of `I (L+1)`
    have hsplit : I (L + 1) = (∑ x, ∑ a, ∑ z', q (L + 1) x (Fin.cons a z') *
        Real.log (q (L + 1) x (Fin.cons a z') / (r x a * ∏ k, c (z' k)))) + I1 := by
      rw [hI, hI1]
      dsimp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sum_fin_succ_fun, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have e : r x a * Real.log (r x a / (ρ x * c a)) = ∑ z', q (L + 1) x (Fin.cons a z') *
          Real.log (r x a / (ρ x * c a)) := by rw [← Finset.sum_mul, hr L x a]
      rw [e, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      set Q := q (L + 1) x (Fin.cons a z')
      rcases (hq0 (L + 1) x (Fin.cons a z')).eq_or_lt with h | h
      · have hQ : Q = 0 := h.symm
        rw [hQ, zero_mul, zero_mul, zero_mul, add_zero]
      · have hR : 0 < r x a := lt_of_lt_of_le h (hqr L x a z')
        have hρx : 0 < ρ x := lt_of_lt_of_le hR (hrle x a).1
        have hca : 0 < c a := lt_of_lt_of_le hR (hrle x a).2
        have hcz : 0 < ∏ k, c (z' k) := by
          have h1 := hqle (L + 1) x (Fin.cons a z')
          rw [Fin.prod_univ_succ, Fin.cons_zero] at h1
          simp only [Fin.cons_succ] at h1
          exact pos_of_mul_pos_right (lt_of_lt_of_le h h1) (hc0 a)
        rw [← mul_add, Real.log_div h.ne' (by positivity), Real.log_div h.ne' (by positivity),
          Real.log_div hR.ne' (by positivity), Real.log_mul hρx.ne' (by positivity),
          Real.log_mul hca.ne' hcz.ne', Real.log_mul hR.ne' hcz.ne',
          Real.log_mul hρx.ne' hca.ne']
        ring
    rw [hsplit]
    -- data processing for `((x, a), z') ↦ (F x a, z')`
    have hdp := klSum_pushSum_le (α := (X × C) × (Fin L → C)) (β := X × (Fin L → C))
      (fun p => (F p.1.1 p.1.2, p.2)) (p := fun p => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2))
      (q := fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k)) (fun p => hq0 _ _ _)
      (fun p => mul_nonneg (hr0 _ _) (Finset.prod_nonneg fun k _ => hc0 _)) fun p h0 => by
        rcases mul_eq_zero.1 h0 with h | h
        · exact le_antisymm (h ▸ hqr L _ _ _) (hq0 _ _ _)
        · have h1 := hqle (L + 1) p.1.1 (Fin.cons p.1.2 p.2)
          rw [Fin.prod_univ_succ, Fin.cons_zero] at h1
          simp only [Fin.cons_succ] at h1
          rw [h, mul_zero] at h1
          exact le_antisymm h1 (hq0 _ _ _)
    have hpush1 : ∀ j z', pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
        (fun p => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2)) (j, z') = q L j z' := by
      intro j z'
      unfold pushSum
      rw [Finset.sum_filter, ← hstat L j z', Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single z']
      · simp only [Prod.mk.injEq, and_true]
      · intro z'' _ hz''
        simp only [Prod.mk.injEq, hz'', and_false, ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hpush2 : ∀ j z', pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
        (fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k)) (j, z') = ρ j * ∏ k, c (z' k) := by
      intro j z'
      unfold pushSum
      rw [Finset.sum_filter, ← hpushr j, Finset.sum_mul, Fintype.sum_prod_type,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single z']
      · by_cases hF : F x a = j
        · simp only [hF, ↓reduceIte]
        · simp only [Prod.mk.injEq, hF, false_and, ↓reduceIte, zero_mul]
      · intro z'' _ hz''
        simp only [Prod.mk.injEq, hz'', and_false, ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hleft : klSum (pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
        (fun p => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2)))
        (pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
          (fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k))) = I L := by
      unfold klSum
      rw [Fintype.sum_prod_type, hI]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z' _ => by
        rw [hpush1, hpush2]
    have hright : klSum (fun p : (X × C) × (Fin L → C) => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2))
        (fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k)) = ∑ x, ∑ a, ∑ z', q (L + 1) x (Fin.cons a z') *
          Real.log (q (L + 1) x (Fin.cons a z') / (r x a * ∏ k, c (z' k))) := by
      unfold klSum
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [hleft, hright] at hdp
    linarith
  -- conclude `I 1 = 0`
  have hlin : ∀ m : ℕ, (m : ℝ) * I1 ≤ I m := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero, zero_mul, hI0]
    | succ m ih =>
      have := hsuper m
      push_cast
      linarith
  have hI1zero : I1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨m, hm⟩ := exists_nat_gt ((∑ x, ρ x * Real.log (1 / ρ x)) / I1)
    have h1 := hlin m
    have h2 := hIle m
    rw [div_lt_iff₀ hpos] at hm
    linarith
  -- Gibbs equality
  have heq := eq_of_klSum_le (α := X × C) (p := fun xa => r xa.1 xa.2)
    (q := fun xa => ρ xa.1 * c xa.2) (fun xa => hr0 _ _) (fun xa => mul_nonneg (hρ0 _) (hc0 _))
    (fun xa h0 => by
      rcases mul_eq_zero.1 h0 with h | h
      · exact le_antisymm (h ▸ (hrle _ _).1) (hr0 _ _)
      · exact le_antisymm (h ▸ (hrle _ _).2) (hr0 _ _))
    (by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [hrX, ← Finset.mul_sum, hc1, mul_one, hρ1])
    (by
      unfold klSum
      rw [Fintype.sum_prod_type]
      exact hI1zero)
  exact congrFun heq (x, a)

/-- **Consequence:** the law `ρ` of `X₀` is stationary for `P x j = ∑_{a : F x a = j} c a`. -/
theorem chentsov_entropy_stationary (F : X → C → X) (c : C → ℝ) (ρ : X → ℝ) (r : X → C → ℝ)
    (q : (m : ℕ) → X → (Fin m → C) → ℝ) (hq0 : ∀ m x z, 0 ≤ q m x z)
    (hZ : ∀ m z, ∑ x, q m x z = ∏ k, c (z k)) (hX : ∀ m x, ∑ z, q m x z = ρ x)
    (hr : ∀ L x a, ∑ z', q (L + 1) x (Fin.cons a z') = r x a)
    (hstat : ∀ L j z', ∑ x, ∑ a, (if F x a = j then q (L + 1) x (Fin.cons a z') else 0) =
      q L j z')
    (hρ1 : ∑ x, ρ x = 1) (j : X) :
    ∑ x, ρ x * (∑ a, if F x a = j then c a else 0) = ρ j := by
  have hind := chentsov_entropy_core F c ρ r q hq0 hZ hX hr hstat hρ1
  rw [← hX 0 j, sum_fin_zero_fun, ← hstat 0 j Fin.elim0]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hra : q (0 + 1) x (Fin.cons a Fin.elim0) = r x a := by
    rw [← hr 0 x a, sum_fin_zero_fun]
  rw [hra, hind x a]
  split_ifs <;> simp only [mul_zero]

end RQMCMarkov.MarkovDriving

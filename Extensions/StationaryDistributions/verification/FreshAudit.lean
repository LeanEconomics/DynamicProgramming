import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Distributions on a finite grid and first-order stochastic dominance

States are the grid points `0, 1, …, n`, in increasing order. A distribution is `ψ : ℕ → ℝ`,
nonnegative with `∑_{i ≤ n} ψ(i) = 1` (values beyond `n` are never used), and a Markov kernel
`P : ℕ → ℕ → ℝ` has a distribution `P(i, ·)` in each row `i ≤ n`.

* `abel`: summation by parts, `∑_{i ≤ m} D_iG_i = ∑_{i < m} F_D(i)(G_i − G_{i+1}) + F_D(m)G_m`,
  the workhorse of the chapter.
* `Dominated ψ φ`: `ψ` is below `φ` in first-order stochastic dominance (`F_ψ ≥ F_φ`), and
  `sum_mul_antitone_le`: then `∑ φG ≤ ∑ ψG` for every decreasing `G` (and the reverse for
  increasing functions, `sum_mul_monotone_le`).
* `IsMonotone P`: the rows of `P` increase in FOSD; `push_mono`: such a kernel preserves FOSD.
* `abs_cdf_push_sub_le`: a monotone kernel shrinks the Kolmogorov distance
  `max_k |F_ψ(k) − F_φ(k)|` by the factor `F_{P(0,·)}(y) − F_{P(n,·)}(y)` at each `y`.
-/

open Finset

namespace DPExtensions.StationaryDistributions

/-- The cumulative distribution function `F_ψ(k) = ∑_{i ≤ k} ψ(i)`. -/
def cdf (ψ : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range (k + 1), ψ i

theorem cdf_zero (ψ : ℕ → ℝ) : cdf ψ 0 = ψ 0 := by simp [cdf]

theorem cdf_succ (ψ : ℕ → ℝ) (k : ℕ) : cdf ψ (k + 1) = cdf ψ k + ψ (k + 1) :=
  sum_range_succ _ _

theorem cdf_sub (ψ φ : ℕ → ℝ) (k : ℕ) : cdf (fun i => ψ i - φ i) k = cdf ψ k - cdf φ k :=
  sum_sub_distrib _ _

/-- **Summation by parts.** -/
theorem abel (D G : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), D i * G i =
      ∑ i ∈ range m, cdf D i * (G i - G (i + 1)) + cdf D m * G m := by
  induction m with
  | zero => simp [cdf]
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ, cdf_succ]
    ring

/-- `ψ` is a distribution on `{0, …, n}`. -/
def IsDist (n : ℕ) (ψ : ℕ → ℝ) : Prop := (∀ i, 0 ≤ ψ i) ∧ cdf ψ n = 1

/-- `P` is a Markov kernel on `{0, …, n}`. -/
def IsKernel (n : ℕ) (P : ℕ → ℕ → ℝ) : Prop := (∀ i j, 0 ≤ P i j) ∧ ∀ i ≤ n, cdf (P i) n = 1

/-- The distribution of the next state, `(ψP)(j) = ∑_{i ≤ n} ψ(i)P(i, j)`. -/
def push (n : ℕ) (ψ : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range (n + 1), ψ i * P i j

/-- The rows of `P` increase in first-order stochastic dominance. -/
def IsMonotone (n : ℕ) (P : ℕ → ℕ → ℝ) : Prop :=
  ∀ i i', i ≤ i' → i' ≤ n → ∀ y ≤ n, cdf (P i') y ≤ cdf (P i) y

/-- `ψ` is below `φ` in first-order stochastic dominance: `F_φ ≤ F_ψ` on the grid. -/
def Dominated (n : ℕ) (ψ φ : ℕ → ℝ) : Prop := ∀ k ≤ n, cdf φ k ≤ cdf ψ k

theorem cdf_nonneg {ψ : ℕ → ℝ} (h : ∀ i, 0 ≤ ψ i) (k : ℕ) : 0 ≤ cdf ψ k :=
  sum_nonneg fun i _ => h i

theorem cdf_mono {ψ : ℕ → ℝ} (h : ∀ i, 0 ≤ ψ i) {k k' : ℕ} (hk : k ≤ k') : cdf ψ k ≤ cdf ψ k' :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun i _ _ => h i

theorem cdf_le_one {n : ℕ} {ψ : ℕ → ℝ} (h : IsDist n ψ) {k : ℕ} (hk : k ≤ n) : cdf ψ k ≤ 1 :=
  h.2 ▸ cdf_mono h.1 hk

/-- `F_{ψP}(y) = ∑_{i ≤ n} ψ(i)F_{P(i, ·)}(y)`. -/
theorem cdf_push (n : ℕ) (ψ : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (y : ℕ) :
    cdf (push n ψ P) y = ∑ i ∈ range (n + 1), ψ i * cdf (P i) y := by
  simp only [cdf, push, mul_sum]
  rw [sum_comm]

theorem push_isDist {n : ℕ} {ψ : ℕ → ℝ} {P : ℕ → ℕ → ℝ} (hψ : IsDist n ψ) (hP : IsKernel n P) :
    IsDist n (push n ψ P) := by
  refine ⟨fun j => sum_nonneg fun i _ => mul_nonneg (hψ.1 i) (hP.1 i j), ?_⟩
  rw [cdf_push, ← hψ.2, cdf]
  exact sum_congr rfl fun i hi => by rw [hP.2 i (by simp at hi; omega), mul_one]

/-- **FOSD and decreasing functions**: if `ψ` is below `φ`, then `∑ φG ≤ ∑ ψG` for every `G`
decreasing on the grid. -/
theorem sum_mul_antitone_le {n : ℕ} {ψ φ : ℕ → ℝ} (hψ : IsDist n ψ) (hφ : IsDist n φ)
    (h : Dominated n ψ φ) {G : ℕ → ℝ} (hG : ∀ i < n, G (i + 1) ≤ G i) :
    ∑ i ∈ range (n + 1), φ i * G i ≤ ∑ i ∈ range (n + 1), ψ i * G i := by
  have e := abel (fun i => ψ i - φ i) G n
  rw [cdf_sub, hψ.2, hφ.2, sub_self, zero_mul, add_zero] at e
  have hnn : 0 ≤ ∑ i ∈ range n, cdf (fun i => ψ i - φ i) i * (G i - G (i + 1)) := by
    refine sum_nonneg fun i hi => mul_nonneg ?_ (sub_nonneg.2 (hG i (mem_range.1 hi)))
    rw [cdf_sub]
    exact sub_nonneg.2 (h i (by simp at hi; omega))
  have e2 : ∑ i ∈ range (n + 1), (ψ i - φ i) * G i =
      ∑ i ∈ range (n + 1), ψ i * G i - ∑ i ∈ range (n + 1), φ i * G i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  linarith

/-- **FOSD and increasing functions**: if `ψ` is below `φ`, then `∑ ψf ≤ ∑ φf` for every `f`
increasing on the grid — for instance mean wealth. -/
theorem sum_mul_monotone_le {n : ℕ} {ψ φ : ℕ → ℝ} (hψ : IsDist n ψ) (hφ : IsDist n φ)
    (h : Dominated n ψ φ) {f : ℕ → ℝ} (hf : ∀ i < n, f i ≤ f (i + 1)) :
    ∑ i ∈ range (n + 1), ψ i * f i ≤ ∑ i ∈ range (n + 1), φ i * f i := by
  have := sum_mul_antitone_le hψ hφ h (G := fun i => -f i) fun i hi => neg_le_neg (hf i hi)
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

/-- **A monotone kernel preserves first-order stochastic dominance.** -/
theorem push_mono {n : ℕ} {P : ℕ → ℕ → ℝ} (hP : IsMonotone n P) {ψ φ : ℕ → ℝ}
    (hψ : IsDist n ψ) (hφ : IsDist n φ) (h : Dominated n ψ φ) :
    Dominated n (push n ψ P) (push n φ P) := by
  intro y hy
  rw [cdf_push, cdf_push]
  exact sum_mul_antitone_le hψ hφ h fun i hi => hP i (i + 1) (Nat.le_succ i) (by omega) y hy

/-- A kernel whose rows are below another's pushes every distribution below. -/
theorem push_le_of_le {n : ℕ} {P Q : ℕ → ℕ → ℝ}
    (hPQ : ∀ i ≤ n, ∀ y ≤ n, cdf (Q i) y ≤ cdf (P i) y) {ψ : ℕ → ℝ} (hψ : ∀ i, 0 ≤ ψ i) :
    Dominated n (push n ψ P) (push n ψ Q) := by
  intro y hy
  rw [cdf_push, cdf_push]
  exact sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hPQ i (by simp at hi; omega) y hy) (hψ i)

/-- **The Kolmogorov distance under a monotone kernel**: if `|F_ψ(k) − F_φ(k)| ≤ δ` on the
grid, then `|F_{ψP}(y) − F_{φP}(y)| ≤ δ(F_{P(0,·)}(y) − F_{P(n,·)}(y))`. -/
theorem abs_cdf_push_sub_le {n : ℕ} {P : ℕ → ℕ → ℝ} (hP : IsMonotone n P) {ψ φ : ℕ → ℝ}
    (hψ : IsDist n ψ) (hφ : IsDist n φ) {δ : ℝ} (hδ : ∀ k ≤ n, |cdf ψ k - cdf φ k| ≤ δ)
    {y : ℕ} (hy : y ≤ n) :
    |cdf (push n ψ P) y - cdf (push n φ P) y| ≤ δ * (cdf (P 0) y - cdf (P n) y) := by
  set G : ℕ → ℝ := fun i => cdf (P i) y
  have e := abel (fun i => ψ i - φ i) G n
  rw [cdf_sub, hψ.2, hφ.2, sub_self, zero_mul, add_zero] at e
  have e2 : cdf (push n ψ P) y - cdf (push n φ P) y =
      ∑ i ∈ range (n + 1), (ψ i - φ i) * G i := by
    rw [cdf_push, cdf_push, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e2, e]
  have hG : ∀ i ∈ range n, 0 ≤ G i - G (i + 1) := fun i hi =>
    sub_nonneg.2 (hP i (i + 1) (Nat.le_succ i) (by simp at hi; omega) y hy)
  calc |∑ i ∈ range n, cdf (fun i => ψ i - φ i) i * (G i - G (i + 1))|
      ≤ ∑ i ∈ range n, |cdf (fun i => ψ i - φ i) i * (G i - G (i + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, δ * (G i - G (i + 1)) := by
        refine sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (hG i hi), cdf_sub]
        exact mul_le_mul_of_nonneg_right (hδ i (by simp at hi; omega)) (hG i hi)
    _ = δ * (G 0 - G n) := by rw [← mul_sum, sum_range_sub']

end DPExtensions.StationaryDistributions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stationary distributions of monotone Markov chains

Hopenhayn and Prescott (1992), "Stochastic monotonicity and stationary distributions for dynamic
economies", on a finite grid; Bhattacharya and Lee (1988) for the
contraction; Kamihigashi and Stachurski (2014) for order mixing.

For a monotone Markov kernel `P` on the grid `{0, …, n}`:

* `exists_least_stationary`: a stationary distribution always exists — the limit of the
  FOSD-increasing sequence `δ₀Pᵗ` — and it is the least one in first-order stochastic dominance.
  No irreducibility or aperiodicity is needed.
* Under the **monotone mixing condition** (`MonotoneMixing`): for some `m`, `c` and `ε > 0`, the
  chain started at the bottom is at or above `c` after `m` steps with probability at least `ε`,
  and the chain started at the top is at or below `c` with probability at least `ε`,
  - `contraction`: `m` steps contract the Kolmogorov distance by `1 − ε`;
  - `stationary_unique`: the stationary distribution is unique;
  - `global_stability`: `ψPᵗ` converges to it from every initial distribution.
* `stationary_mono` (**comparative statics**): if `P` is below `Q` row by row in FOSD, both
  monotone, and `P` mixes, then `P`'s stationary distribution is below every stationary
  distribution of `Q` — so the mean of every increasing function is lower.
-/

open Finset Filter Topology

namespace DPExtensions.StationaryDistributions

variable {n : ℕ} {P : ℕ → ℕ → ℝ}

/-- The `m`-step kernel `Pᵐ`. -/
def kpow (n : ℕ) (P : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun i j => if i = j then 1 else 0
  | m + 1 => fun i j => ∑ k ∈ range (n + 1), kpow n P m i k * P k j

/-- The distribution `ψPᵗ` after `t` steps. -/
def iter (n : ℕ) (P : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => ψ
  | t + 1 => push n (iter n P ψ t) P

/-- `ψ` is stationary for `P` on the grid. -/
def IsStationary (n : ℕ) (P : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) : Prop := ∀ j ≤ n, push n ψ P j = ψ j

theorem cdf_congr {ψ φ : ℕ → ℝ} {k : ℕ} (h : ∀ i ≤ k, ψ i = φ i) : cdf ψ k = cdf φ k :=
  sum_congr rfl fun i hi => h i (by simp at hi; omega)

theorem push_congr {ψ φ : ℕ → ℝ} (h : ∀ i ≤ n, ψ i = φ i) (j : ℕ) :
    push n ψ P j = push n φ P j :=
  sum_congr rfl fun i hi => by rw [h i (by simp at hi; omega)]

theorem eq_cdf_sub (ψ : ℕ → ℝ) (j : ℕ) : ψ (j + 1) = cdf ψ (j + 1) - cdf ψ j := by
  rw [cdf_succ]
  ring

theorem cdf_kpow_zero (i y : ℕ) : cdf (kpow n P 0 i) y = if i ≤ y then 1 else 0 := by
  simp only [cdf, kpow]
  rw [sum_ite_eq]
  simp only [mem_range]
  split_ifs <;> first | rfl | omega

theorem kpow_isKernel (hP : IsKernel n P) (m : ℕ) : IsKernel n (kpow n P m) := by
  induction m with
  | zero =>
    refine ⟨fun i j => by simp only [kpow]; split_ifs <;> norm_num, fun i hi => ?_⟩
    rw [cdf_kpow_zero]
    simp [hi]
  | succ m ih =>
    refine ⟨fun i j => sum_nonneg fun k _ => mul_nonneg (ih.1 i k) (hP.1 k j), fun i hi => ?_⟩
    exact (push_isDist ⟨ih.1 i, ih.2 i hi⟩ hP).2

theorem kpow_isMonotone (hP : IsKernel n P) (hm : IsMonotone n P) (m : ℕ) :
    IsMonotone n (kpow n P m) := by
  induction m with
  | zero =>
    intro i i' hii' _ y _
    rw [cdf_kpow_zero, cdf_kpow_zero]
    split_ifs <;> first | omega | norm_num
  | succ m ih =>
    intro i i' hii' hi' y hy
    have hk := kpow_isKernel hP m
    exact push_mono hm ⟨hk.1 i, hk.2 i (by omega)⟩ ⟨hk.1 i', hk.2 i' hi'⟩
      (fun k hk' => ih i i' hii' hi' k hk') y hy

theorem iter_eq_push_kpow (ψ : ℕ → ℝ) (m : ℕ) :
    ∀ j ≤ n, iter n P ψ m j = push n ψ (kpow n P m) j := by
  induction m with
  | zero =>
    intro j hj
    simp only [iter, push, kpow, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq']
    simp [show j < n + 1 by omega]
  | succ m ih =>
    intro j _
    simp only [iter]
    rw [push_congr ih j]
    simp only [push, kpow, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

theorem iter_add (ψ : ℕ → ℝ) (t m : ℕ) : iter n P ψ (t + m) = iter n P (iter n P ψ t) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, iter, ih, iter]

theorem iter_isDist (hP : IsKernel n P) {ψ : ℕ → ℝ} (hψ : IsDist n ψ) (t : ℕ) :
    IsDist n (iter n P ψ t) := by
  induction t with
  | zero => exact hψ
  | succ t ih => exact push_isDist ih hP

theorem iter_stationary {ψ : ℕ → ℝ} (hψ : IsStationary n P ψ) (t : ℕ) :
    ∀ j ≤ n, iter n P ψ t j = ψ j := by
  induction t with
  | zero => exact fun _ _ => rfl
  | succ t ih => exact fun j hj => (push_congr ih j).trans (hψ j hj)

/-- One step of a monotone kernel does not increase the Kolmogorov distance. -/
theorem nonexpansive (hP : IsKernel n P) (hm : IsMonotone n P) {ψ φ : ℕ → ℝ}
    (hψ : IsDist n ψ) (hφ : IsDist n φ) {δ : ℝ} (hδ : ∀ k ≤ n, |cdf ψ k - cdf φ k| ≤ δ) :
    ∀ y ≤ n, |cdf (push n ψ P) y - cdf (push n φ P) y| ≤ δ := by
  intro y hy
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0 (Nat.zero_le n))
  refine (abs_cdf_push_sub_le hm hψ hφ hδ hy).trans ?_
  have h1 := cdf_le_one ⟨hP.1 0, hP.2 0 (Nat.zero_le n)⟩ hy
  have h2 := cdf_nonneg (hP.1 n) y
  nlinarith

/-! ### Existence -/

/-- The point mass at the bottom state. -/
def bottom : ℕ → ℝ := fun i => if i = 0 then 1 else 0

theorem cdf_bottom (k : ℕ) : cdf bottom k = 1 := by
  simp only [cdf, bottom]
  rw [sum_ite_eq']
  simp

theorem bottom_isDist : IsDist n bottom :=
  ⟨fun i => by simp only [bottom]; split_ifs <;> norm_num, cdf_bottom n⟩

theorem bottom_le {ψ : ℕ → ℝ} (hψ : IsDist n ψ) : Dominated n bottom ψ := fun k hk => by
  rw [cdf_bottom]
  exact cdf_le_one hψ hk

/-- **Hopenhayn and Prescott (1992)**: a monotone kernel has a stationary distribution, the
limit of `δ₀Pᵗ`, which lies below every stationary distribution in FOSD. -/
theorem exists_least_stationary (hP : IsKernel n P) (hm : IsMonotone n P) :
    ∃ ψ, IsDist n ψ ∧ IsStationary n P ψ ∧ ∀ φ, IsDist n φ → IsStationary n P φ →
      Dominated n ψ φ := by
  set ψt := iter n P bottom
  have hd : ∀ t, IsDist n (ψt t) := iter_isDist hP bottom_isDist
  -- the cdfs decrease in `t`
  have hstep : ∀ t, Dominated n (ψt t) (ψt (t + 1)) := by
    intro t
    induction t with
    | zero => exact bottom_le (hd 1)
    | succ t ih => exact push_mono hm (hd t) (hd (t + 1)) ih
  have hanti : ∀ k ≤ n, Antitone fun t => cdf (ψt t) k := fun k hk =>
    antitone_nat_of_succ_le fun t => hstep t k hk
  have hlim : ∀ k ≤ n, Tendsto (fun t => cdf (ψt t) k) atTop
      (𝓝 (⨅ t, cdf (ψt t) k)) := fun k hk =>
    tendsto_atTop_ciInf (hanti k hk) ⟨0, fun _ ⟨t, ht⟩ => ht ▸ cdf_nonneg (hd t).1 k⟩
  set F : ℕ → ℝ := fun k => ⨅ t, cdf (ψt t) k
  set ψ : ℕ → ℝ := fun j => if j ≤ n then (if j = 0 then F 0 else F j - F (j - 1)) else 0
  -- `ψPᵗ → ψ` pointwise on the grid
  have hconv : ∀ j ≤ n, Tendsto (fun t => ψt t j) atTop (𝓝 (ψ j)) := by
    intro j hj
    simp only [ψ, hj, ↓reduceIte]
    rcases j with _ | j
    · simp only [↓reduceIte]
      have e : (fun t => ψt t 0) = fun t => cdf (ψt t) 0 := funext fun t => (cdf_zero _).symm
      rw [e]
      exact hlim 0 (Nat.zero_le n)
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have e : (fun t => ψt t (j + 1)) = fun t => cdf (ψt t) (j + 1) - cdf (ψt t) j :=
        funext fun t => eq_cdf_sub _ _
      rw [e]
      exact (hlim (j + 1) hj).sub (hlim j (by omega))
  have hcdf : ∀ k ≤ n, cdf ψ k = F k := by
    intro k hk
    induction k with
    | zero => simp [cdf_zero, ψ]
    | succ k ih =>
      rw [cdf_succ, ih (by omega)]
      simp only [ψ, hk, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      ring
  have hdist : IsDist n ψ := by
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j ≤ n
      · exact ge_of_tendsto' (hconv j hj) fun t => (hd t).1 j
      · simp only [ψ, hj, ↓reduceIte, le_refl]
    · rw [hcdf n le_rfl]
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (F n)) :=
        (hlim n le_rfl).congr fun t => (hd t).2
      exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hstat : IsStationary n P ψ := by
    intro j hj
    have h1 : Tendsto (fun t => push n (ψt t) P j) atTop (𝓝 (push n ψ P j)) :=
      tendsto_finsetSum _ fun i hi => (hconv i (by simp at hi; omega)).mul_const _
    have h2 : Tendsto (fun t => push n (ψt t) P j) atTop (𝓝 (ψ j)) :=
      (hconv j hj).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 h2
  refine ⟨ψ, hdist, hstat, fun φ hφ hφs k hk => ?_⟩
  -- `δ₀Pᵗ ≤ φPᵗ = φ`, so the limit is below `φ`
  have hle : ∀ t, Dominated n (ψt t) (iter n P φ t) := by
    intro t
    induction t with
    | zero => exact bottom_le hφ
    | succ t ih => exact push_mono hm (hd t) (iter_isDist hP hφ t) ih
  rw [hcdf k hk]
  refine ge_of_tendsto' (hlim k hk) fun t => ?_
  have := hle t k hk
  rwa [cdf_congr fun i hi => iter_stationary hφs t i (by omega)] at this

/-! ### Uniqueness and global stability under monotone mixing -/

/-- **Monotone mixing** (Hopenhayn and Prescott, 1992): after `m` steps the chain
started at the bottom is at or above `c` with probability at least `ε`, and the chain started at
the top is at or below `c` with probability at least `ε`. -/
def MonotoneMixing (n : ℕ) (P : ℕ → ℕ → ℝ) : Prop :=
  ∃ (m c : ℕ) (ε : ℝ), 0 < ε ∧ c ≤ n ∧ (∀ y < c, cdf (kpow n P m 0) y ≤ 1 - ε) ∧
    ε ≤ cdf (kpow n P m n) c

/-- **The contraction** (Bhattacharya and Lee, 1988): under monotone mixing, `m` steps shrink the
Kolmogorov distance by `1 − ε`. -/
theorem contraction (hP : IsKernel n P) (hm : IsMonotone n P) {m c : ℕ} {ε : ℝ}
    (hlow : ∀ y < c, cdf (kpow n P m 0) y ≤ 1 - ε)
    (hhigh : ε ≤ cdf (kpow n P m n) c) {ψ φ : ℕ → ℝ} (hψ : IsDist n ψ) (hφ : IsDist n φ)
    {δ : ℝ} (hδ : ∀ k ≤ n, |cdf ψ k - cdf φ k| ≤ δ) :
    ∀ y ≤ n, |cdf (iter n P ψ m) y - cdf (iter n P φ m) y| ≤ (1 - ε) * δ := by
  intro y hy
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0 (Nat.zero_le n))
  have hk := kpow_isKernel hP m
  rw [cdf_congr fun i hi => iter_eq_push_kpow ψ m i (by omega),
    cdf_congr fun i hi => iter_eq_push_kpow φ m i (by omega)]
  refine (abs_cdf_push_sub_le (kpow_isMonotone hP hm m) hψ hφ hδ hy).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hδ0
  rcases lt_or_ge y c with h | h
  · linarith [hlow y h, cdf_nonneg (hk.1 n) y]
  · linarith [cdf_le_one ⟨hk.1 0, hk.2 0 (Nat.zero_le n)⟩ hy,
      cdf_mono (hk.1 n) h]

/-- The Kolmogorov distance on the grid. -/
noncomputable def kdist (n : ℕ) (ψ φ : ℕ → ℝ) : ℝ :=
  (range (n + 1)).sup' nonempty_range_add_one fun k => |cdf ψ k - cdf φ k|

theorem le_kdist (ψ φ : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) : |cdf ψ k - cdf φ k| ≤ kdist n ψ φ :=
  le_sup' (fun k => |cdf ψ k - cdf φ k|) (mem_range.2 (by omega))

theorem kdist_le {ψ φ : ℕ → ℝ} {δ : ℝ} (h : ∀ k ≤ n, |cdf ψ k - cdf φ k| ≤ δ) :
    kdist n ψ φ ≤ δ :=
  sup'_le _ _ fun k hk => h k (by simp at hk; omega)

theorem eq_of_cdf_eq {ψ φ : ℕ → ℝ} (h : ∀ k ≤ n, cdf ψ k = cdf φ k) : ∀ j ≤ n, ψ j = φ j := by
  intro j hj
  rcases j with _ | j
  · rw [← cdf_zero ψ, ← cdf_zero φ, h 0 hj]
  · rw [eq_cdf_sub ψ, eq_cdf_sub φ, h _ hj, h j (by omega)]

/-- **Uniqueness** of the stationary distribution under monotone mixing. -/
theorem stationary_unique (hP : IsKernel n P) (hm : IsMonotone n P) (hmix : MonotoneMixing n P)
    {ψ φ : ℕ → ℝ} (hψ : IsDist n ψ) (hφ : IsDist n φ) (hψs : IsStationary n P ψ)
    (hφs : IsStationary n P φ) : ∀ j ≤ n, ψ j = φ j := by
  obtain ⟨m, c, ε, hε, hc, hlow, hhigh⟩ := hmix
  have hcon := contraction hP hm hlow hhigh hψ hφ fun k hk => le_kdist ψ φ hk
  have h1 : kdist n ψ φ ≤ (1 - ε) * kdist n ψ φ := kdist_le fun k hk => by
    have := hcon k hk
    rwa [cdf_congr fun i hi => iter_stationary hψs m i (by omega),
      cdf_congr fun i hi => iter_stationary hφs m i (by omega)] at this
  have h0 : 0 ≤ kdist n ψ φ := (abs_nonneg _).trans (le_kdist ψ φ (Nat.zero_le n))
  have h2 : kdist n ψ φ = 0 := by nlinarith
  refine eq_of_cdf_eq fun k hk => ?_
  have := le_kdist ψ φ hk
  rw [h2] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- **Global stability** (Hopenhayn and Prescott, 1992): under monotone mixing, `ψPᵗ`
converges to the stationary distribution from every initial distribution `ψ`. -/
theorem global_stability (hP : IsKernel n P) (hm : IsMonotone n P) (hmix : MonotoneMixing n P)
    {ψstar : ℕ → ℝ} (hd : IsDist n ψstar) (hs : IsStationary n P ψstar) {ψ : ℕ → ℝ}
    (hψ : IsDist n ψ) : ∀ j ≤ n, Tendsto (fun t => iter n P ψ t j) atTop (𝓝 (ψstar j)) := by
  obtain ⟨m, c, ε, hε, hc, hlow, hhigh⟩ := hmix
  set e : ℕ → ℝ := fun t => kdist n (iter n P ψ t) ψstar
  have hdt := iter_isDist hP hψ
  have he0 : ∀ t, 0 ≤ e t := fun t => (abs_nonneg _).trans (le_kdist _ _ (Nat.zero_le n))
  have hstar : ∀ t, ∀ k ≤ n, cdf (iter n P ψstar t) k = cdf ψstar k := fun t k _ =>
    cdf_congr fun i hi => iter_stationary hs t i (by omega)
  have hmono : Antitone e := antitone_nat_of_succ_le fun t => kdist_le fun k hk => by
    have := nonexpansive hP hm (hdt t) hd (fun k hk => le_kdist _ _ hk) k hk
    rwa [show push n ψstar P = iter n P ψstar 1 from rfl, hstar 1 k hk] at this
  have hstepm : ∀ t, e (t + m) ≤ (1 - ε) * e t := fun t => kdist_le fun k hk => by
    have := contraction hP hm hlow hhigh (hdt t) hd (fun k hk => le_kdist _ _ hk) k hk
    rwa [← iter_add, hstar m k hk] at this
  have hε1 : ε ≤ 1 := hhigh.trans (cdf_le_one ⟨(kpow_isKernel hP m).1 n,
    (kpow_isKernel hP m).2 n le_rfl⟩ hc)
  have hgeo : ∀ s, e (m * s) ≤ (1 - ε) ^ s * e 0 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [mul_add, mul_one, pow_succ]
      calc e (m * s + m) ≤ (1 - ε) * e (m * s) := hstepm _
        _ ≤ (1 - ε) * ((1 - ε) ^ s * e 0) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - ε) ^ s * (1 - ε) * e 0 := by ring
  have hlim : Tendsto e atTop (𝓝 0) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · have : ∀ t, e t = 0 := fun t => by
        have h := hstepm t
        rw [hm0, add_zero] at h
        nlinarith [he0 t]
      rw [show e = fun _ => 0 from funext this]
      exact tendsto_const_nhds
    · have hpow : Tendsto (fun s : ℕ => (1 - ε) ^ s * e 0) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const
          (e 0)
      have hdiv : Tendsto (fun t => t / m) atTop atTop := Nat.tendsto_div_const_atTop hm0.ne'
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hpow.comp hdiv) he0
        fun t => ?_
      exact (hmono (Nat.mul_div_le t m)).trans (hgeo _)
  have hcdf : ∀ k ≤ n, Tendsto (fun t => cdf (iter n P ψ t) k) atTop (𝓝 (cdf ψstar k)) := by
    intro k hk
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun t => dist_nonneg) fun t => ?_
    rw [Real.dist_eq]
    exact le_kdist _ _ hk
  intro j hj
  rcases j with _ | j
  · have e1 : (fun t => iter n P ψ t 0) = fun t => cdf (iter n P ψ t) 0 :=
      funext fun t => (cdf_zero _).symm
    rw [e1, ← cdf_zero ψstar]
    exact hcdf 0 hj
  · have e1 : (fun t => iter n P ψ t (j + 1)) =
        fun t => cdf (iter n P ψ t) (j + 1) - cdf (iter n P ψ t) j :=
      funext fun t => eq_cdf_sub _ _
    rw [e1, eq_cdf_sub ψstar]
    exact (hcdf (j + 1) hj).sub (hcdf j (by omega))

/-! ### Comparative statics -/

/-- **Monotone comparative statics of stationary distributions** (Hopenhayn and Prescott,
1992): if `P` is below `Q` row by row in FOSD, both are monotone kernels and `P` satisfies
monotone mixing, then `P`'s stationary distribution is below any stationary distribution of
`Q`, and the mean of every increasing function is lower. -/
theorem stationary_mono {Q : ℕ → ℕ → ℝ} (hP : IsKernel n P) (hm : IsMonotone n P)
    (hmix : MonotoneMixing n P)
    (hPQ : ∀ i ≤ n, ∀ y ≤ n, cdf (Q i) y ≤ cdf (P i) y)
    {ψP ψQ : ℕ → ℝ} (hdP : IsDist n ψP) (hsP : IsStationary n P ψP) (hdQ : IsDist n ψQ)
    (hsQ : IsStationary n Q ψQ) :
    Dominated n ψP ψQ ∧ ∀ f : ℕ → ℝ, (∀ i < n, f i ≤ f (i + 1)) →
      ∑ i ∈ range (n + 1), ψP i * f i ≤ ∑ i ∈ range (n + 1), ψQ i * f i := by
  have hdt := iter_isDist hP hdQ
  -- `ψ_Q Pᵗ` decreases in FOSD, starting from `ψ_Q`
  have hdec : ∀ t, Dominated n (iter n P ψQ t) ψQ := by
    intro t
    induction t with
    | zero => exact fun k _ => le_rfl
    | succ t ih =>
      intro k hk
      have h1 := push_mono hm (hdt t) hdQ ih k hk
      have h2 := push_le_of_le hPQ hdQ.1 k hk
      rw [cdf_congr fun i hi => hsQ i (by omega)] at h2
      exact h2.trans h1
  have hdom : Dominated n ψP ψQ := by
    intro k hk
    have hconv := global_stability hP hm hmix hdP hsP hdQ
    have hc : Tendsto (fun t => cdf (iter n P ψQ t) k) atTop (𝓝 (cdf ψP k)) :=
      tendsto_finsetSum _ fun i hi => hconv i (by simp at hi; omega)
    exact ge_of_tendsto' hc fun t => hdec t k hk
  exact ⟨hdom, fun f hf => sum_mul_monotone_le hdP hdQ hdom hf⟩

end DPExtensions.StationaryDistributions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset distributions induced by saving rules

In a Bewley–Huggett–Aiyagari economy with i.i.d. income `z ∼ π`, a household with assets at grid
point `i` and income `z` moves to grid point `σ(i, z)`. Assets then follow the Markov chain
`P_σ(i, j) = ∑_z π(z)𝟙{σ(i, z) = j}` (`policyKernel`).

* `policyKernel_isKernel`, `policyKernel_isMonotone`: `P_σ` is a Markov kernel, and it is
  monotone when `σ` is increasing in assets — the conclusion of Topkis's theorem for the savings
  problem (`Extensions/MonotonePolicies`).
* `policyKernel_le`: a pointwise higher saving rule gives FOSD-higher rows.
* `aggregate_assets_mono`: if `σ ≤ σ'` are increasing saving rules and `P_σ` satisfies monotone
  mixing, the stationary asset distribution under `σ` is below every stationary distribution
  under `σ'`, so aggregate assets `∑ ψ(i) level(i)` are lower. This is the monotonicity of
  aggregate capital supply in any parameter that raises the saving rule.
-/

open Finset Filter Topology

namespace DPExtensions.StationaryDistributions

variable {Z : Type*} [Fintype Z] {n : ℕ}

/-- The asset chain under the saving rule `σ` with i.i.d. income `π`. -/
def policyKernel (π : Z → ℝ) (σ : ℕ → Z → ℕ) (i j : ℕ) : ℝ :=
  ∑ z, π z * if σ i z = j then 1 else 0

theorem cdf_policyKernel (π : Z → ℝ) (σ : ℕ → Z → ℕ) (i y : ℕ) :
    cdf (policyKernel π σ i) y = ∑ z, π z * if σ i z ≤ y then 1 else 0 := by
  simp only [cdf, policyKernel]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum, sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

theorem policyKernel_isKernel {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1)
    {σ : ℕ → Z → ℕ} (hσ : ∀ i ≤ n, ∀ z, σ i z ≤ n) : IsKernel n (policyKernel π σ) := by
  refine ⟨fun i j => sum_nonneg fun z _ => mul_nonneg (hπ0 z) (by split_ifs <;> norm_num),
    fun i hi => ?_⟩
  rw [cdf_policyKernel]
  calc ∑ z, π z * (if σ i z ≤ n then (1 : ℝ) else 0) = ∑ z, π z :=
        sum_congr rfl fun z _ => by simp [hσ i hi z]
    _ = 1 := hπ1

/-- An increasing saving rule gives a monotone asset chain. -/
theorem policyKernel_isMonotone {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) {σ : ℕ → Z → ℕ}
    (hσ : ∀ z, Monotone fun i => σ i z) : IsMonotone n (policyKernel π σ) := by
  intro i i' hii' _ y _
  rw [cdf_policyKernel, cdf_policyKernel]
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hπ0 z)
  have := hσ z hii'
  simp only at this
  split_ifs <;> first | omega | norm_num

/-- A pointwise higher saving rule has FOSD-higher rows. -/
theorem policyKernel_le {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) {σ σ' : ℕ → Z → ℕ}
    (h : ∀ i z, σ i z ≤ σ' i z) (i y : ℕ) :
    cdf (policyKernel π σ' i) y ≤ cdf (policyKernel π σ i) y := by
  rw [cdf_policyKernel, cdf_policyKernel]
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hπ0 z)
  have := h i z
  split_ifs <;> first | omega | norm_num

/-- **Aggregate assets rise with the saving rule.** If `σ ≤ σ'` and `P_σ` is monotone and
mixing, the stationary asset distribution under `σ` is FOSD-below every stationary distribution
under `σ'`, and aggregate assets `∑_i ψ(i)·level(i)` are lower for every increasing grid
`level`. -/
theorem aggregate_assets_mono {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1)
    {σ σ' : ℕ → Z → ℕ} (hσn : ∀ i ≤ n, ∀ z, σ i z ≤ n)
    (hσm : ∀ z, Monotone fun i => σ i z) (hσσ' : ∀ i z, σ i z ≤ σ' i z)
    (hmix : MonotoneMixing n (policyKernel π σ)) {ψ ψ' : ℕ → ℝ} (hd : IsDist n ψ)
    (hs : IsStationary n (policyKernel π σ) ψ) (hd' : IsDist n ψ')
    (hs' : IsStationary n (policyKernel π σ') ψ') {level : ℕ → ℝ}
    (hlevel : ∀ i < n, level i ≤ level (i + 1)) :
    Dominated n ψ ψ' ∧
      ∑ i ∈ range (n + 1), ψ i * level i ≤ ∑ i ∈ range (n + 1), ψ' i * level i := by
  have h := stationary_mono (policyKernel_isKernel hπ0 hπ1 hσn) (policyKernel_isMonotone hπ0 hσm)
    hmix (fun i _ y _ => policyKernel_le hπ0 hσσ' i y) hd hs hd' hs'
  exact ⟨h.1, h.2 level hlevel⟩

end DPExtensions.StationaryDistributions

set_option linter.style.longLine false
#print axioms DPExtensions.StationaryDistributions.cdf
#print axioms DPExtensions.StationaryDistributions.cdf_zero
#print axioms DPExtensions.StationaryDistributions.cdf_succ
#print axioms DPExtensions.StationaryDistributions.cdf_sub
#print axioms DPExtensions.StationaryDistributions.abel
#print axioms DPExtensions.StationaryDistributions.IsDist
#print axioms DPExtensions.StationaryDistributions.IsKernel
#print axioms DPExtensions.StationaryDistributions.push
#print axioms DPExtensions.StationaryDistributions.IsMonotone
#print axioms DPExtensions.StationaryDistributions.Dominated
#print axioms DPExtensions.StationaryDistributions.cdf_nonneg
#print axioms DPExtensions.StationaryDistributions.cdf_mono
#print axioms DPExtensions.StationaryDistributions.cdf_le_one
#print axioms DPExtensions.StationaryDistributions.cdf_push
#print axioms DPExtensions.StationaryDistributions.push_isDist
#print axioms DPExtensions.StationaryDistributions.sum_mul_antitone_le
#print axioms DPExtensions.StationaryDistributions.sum_mul_monotone_le
#print axioms DPExtensions.StationaryDistributions.push_mono
#print axioms DPExtensions.StationaryDistributions.push_le_of_le
#print axioms DPExtensions.StationaryDistributions.abs_cdf_push_sub_le
#print axioms DPExtensions.StationaryDistributions.kpow
#print axioms DPExtensions.StationaryDistributions.iter
#print axioms DPExtensions.StationaryDistributions.IsStationary
#print axioms DPExtensions.StationaryDistributions.cdf_congr
#print axioms DPExtensions.StationaryDistributions.push_congr
#print axioms DPExtensions.StationaryDistributions.eq_cdf_sub
#print axioms DPExtensions.StationaryDistributions.cdf_kpow_zero
#print axioms DPExtensions.StationaryDistributions.kpow_isKernel
#print axioms DPExtensions.StationaryDistributions.kpow_isMonotone
#print axioms DPExtensions.StationaryDistributions.iter_eq_push_kpow
#print axioms DPExtensions.StationaryDistributions.iter_add
#print axioms DPExtensions.StationaryDistributions.iter_isDist
#print axioms DPExtensions.StationaryDistributions.iter_stationary
#print axioms DPExtensions.StationaryDistributions.nonexpansive
#print axioms DPExtensions.StationaryDistributions.bottom
#print axioms DPExtensions.StationaryDistributions.cdf_bottom
#print axioms DPExtensions.StationaryDistributions.bottom_isDist
#print axioms DPExtensions.StationaryDistributions.bottom_le
#print axioms DPExtensions.StationaryDistributions.exists_least_stationary
#print axioms DPExtensions.StationaryDistributions.MonotoneMixing
#print axioms DPExtensions.StationaryDistributions.contraction
#print axioms DPExtensions.StationaryDistributions.kdist
#print axioms DPExtensions.StationaryDistributions.le_kdist
#print axioms DPExtensions.StationaryDistributions.kdist_le
#print axioms DPExtensions.StationaryDistributions.eq_of_cdf_eq
#print axioms DPExtensions.StationaryDistributions.stationary_unique
#print axioms DPExtensions.StationaryDistributions.global_stability
#print axioms DPExtensions.StationaryDistributions.stationary_mono
#print axioms DPExtensions.StationaryDistributions.policyKernel
#print axioms DPExtensions.StationaryDistributions.cdf_policyKernel
#print axioms DPExtensions.StationaryDistributions.policyKernel_isKernel
#print axioms DPExtensions.StationaryDistributions.policyKernel_isMonotone
#print axioms DPExtensions.StationaryDistributions.policyKernel_le
#print axioms DPExtensions.StationaryDistributions.aggregate_assets_mono

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StationaryDistributions.CDF
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

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

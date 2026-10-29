/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.CountableClassification
import Mathlib.Analysis.PSeries

/-!
# Independent coupling fails for null chains (MT §18.1, p. 464)

Meyn and Tweedie, p. 464. The book explains why the coupling of §13.2, which runs two renewal
processes independently until they renew at the same time, needs a finite mean. The simple
symmetric random walk on `ℤ²` is recurrent, so its return times to the origin form a proper
renewal process. Two independent copies of it form a random walk on `ℤ⁴` which is transient, so
the joint renewal time (the coupling time) is infinite with positive probability. Following
Spitzer, this is proved through the 45° rotation of `ℤ²`.

**Matrices.**
* `prodMat p q`: the matrix of two independent chains; `matPow_prodMat`: the `n`-step
  probabilities multiply; `isTransitionMatrix_prodMat`.
* `matPow_eq_of_injective`: `n`-step probabilities are preserved by an injection that
  intertwines one step and from whose range the target chain does not step out.

**The walk on `ℤ`.** `ssrw1`; `tsum_ssrw1_mul` (one step); `ssrwCount n d`, the number of
`±1` paths with displacement `d`, with Pascal's rule `ssrwCount_succ`; `matPow_ssrw1`:
`Pⁿ(x, z) = 2⁻ⁿ ssrwCount n (z − x)`; `matPow_ssrw1_even`: `P²ⁿ(x, x) = C(2n, n)/4ⁿ`;
`matPow_ssrw1_odd`: `P²ⁿ⁺¹(x, x) = 0`.

**The walk on `ℤ²`.** `ssrw2` (steps to the four neighbours); `rot (a, b) = (a + b, a − b)`
maps `ℤ²` onto the even sublattice, and `ssrw2_eq_prodMat`: one step of `ssrw2` is a step
`(±1, ±1)` of two independent walks on `ℤ`; hence `matPow_ssrw2` and
`matPow_ssrw2_even`: `P²ⁿ(u, u) = c_n²` with `c_n = C(2n, n)/4ⁿ`.

**Two copies of the walk on `ℤ²`.** `ssrw4 = prodMat ssrw2 ssrw2`, a walk on `ℤ⁴`;
`matKernel_ssrw4`: its law from `(x, y)` is `P(x, ·) ⊗ P(y, ·)` (independent copies);
`matKernel_ssrw4_pow`; `matPow_ssrw4_even`: `P²ⁿ(w, w) = c_n⁴`.

**Bounds.** `centralC n = c_n`; `centralC_succ`: `c_{n+1} = c_n (2n + 1)/(2n + 2)`;
`centralC_sq_le`: `c_n² ≤ 1/(2n + 1)`; `centralC_sq_ge`: `c_{n+1}² ≥ 1/(4(n + 1))`.

**Results** (with the Chapter 8 classification by `U(x, x) = Σₙ Pⁿ(x, x)`).
* `ssrw2_isRecurrentState`: the walk on `ℤ²` is recurrent (`Σ c_n² = ∞`).
* `ssrw4_isTransientState`: the walk on `ℤ⁴` made of two independent copies is transient
  (`Σ c_n⁴ < ∞`).
* `independent_coupling_fails`: the return-time renewal process of the `ℤ²` walk is proper,
  `L(u, u) = 1`, but two independent copies started at `u` renew together with probability
  `L((u, u), (u, u)) < 1`, so the joint renewal time is infinite with positive probability.

**Correction.** None.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-! ### Products and pull-backs of transition matrices -/

/-- The matrix of two independent chains: `(p ⊗ q)((x, y), (x', y')) = p(x, x') q(y, y')`. -/
noncomputable def prodMat {X Y : Type*} (p : X → X → ℝ≥0∞) (q : Y → Y → ℝ≥0∞)
    (u v : X × Y) : ℝ≥0∞ :=
  p u.1 v.1 * q u.2 v.2

/-- **The `n`-step probabilities of independent chains multiply**:
`(p ⊗ q)ⁿ((x, y), (x', y')) = pⁿ(x, x') qⁿ(y, y')`. -/
theorem matPow_prodMat {X Y : Type*} (p : X → X → ℝ≥0∞) (q : Y → Y → ℝ≥0∞) (n : ℕ)
    (u v : X × Y) : matPow (prodMat p q) n u v = matPow p n u.1 v.1 * matPow q n u.2 v.2 := by
  induction n generalizing u with
  | zero =>
    rcases u with ⟨x, y⟩
    rcases v with ⟨x', y'⟩
    simp only [matPow]
    by_cases hx : x = x' <;> by_cases hy : y = y' <;> simp [hx, hy]
  | succ n ih =>
    simp only [matPow]
    simp_rw [ih, prodMat]
    rw [ENNReal.tsum_prod (f := fun a b => p u.1 a * q u.2 b *
      (matPow p n a v.1 * matPow q n b v.2))]
    have h : ∀ a b, p u.1 a * q u.2 b * (matPow p n a v.1 * matPow q n b v.2) =
        (p u.1 a * matPow p n a v.1) * (q u.2 b * matPow q n b v.2) := fun a b => by ring
    simp_rw [h, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- The product of transition matrices is a transition matrix. -/
theorem isTransitionMatrix_prodMat {X Y : Type*} {p : X → X → ℝ≥0∞} {q : Y → Y → ℝ≥0∞}
    (hp : IsTransitionMatrix p) (hq : IsTransitionMatrix q) : IsTransitionMatrix (prodMat p q) :=
  fun u => by
    simp_rw [prodMat]
    rw [ENNReal.tsum_prod (f := fun a b => p u.1 a * q u.2 b)]
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hq u.2, mul_one, hp u.1]

/-- **Pull-back along an injection**: if `p(x, x') = q(Rx, Rx')` and `q` never leaves the range
of `R` from a point of it, then `pⁿ(x, z) = qⁿ(Rx, Rz)`. -/
theorem matPow_eq_of_injective {X Y : Type*} {p : X → X → ℝ≥0∞} {q : Y → Y → ℝ≥0∞}
    {R : X → Y} (hR : Function.Injective R) (hpq : ∀ x x', p x x' = q (R x) (R x'))
    (hsupp : ∀ x u, q (R x) u ≠ 0 → u ∈ range R) (n : ℕ) (x z : X) :
    matPow p n x z = matPow q n (R x) (R z) := by
  induction n generalizing x with
  | zero =>
    simp only [matPow]
    by_cases h : x = z
    · simp [h]
    · simp [h, hR.ne h]
  | succ n ih =>
    simp only [matPow]
    simp_rw [hpq, ih]
    exact hR.tsum_eq (f := fun u => q (R x) u * matPow q n u (R z))
      (fun u hu => hsupp x u (left_ne_zero_of_mul hu))

/-! ### The simple symmetric random walk on `ℤ` -/

/-- The simple symmetric random walk on `ℤ`: steps `±1` with probability `½` each. -/
noncomputable def ssrw1 (x y : ℤ) : ℝ≥0∞ := if y - x = 1 ∨ y - x = -1 then 2⁻¹ else 0

/-- One step of the walk: `Σ_y P(x, y) g(y) = ½ g(x + 1) + ½ g(x − 1)`. -/
theorem tsum_ssrw1_mul (x : ℤ) (g : ℤ → ℝ≥0∞) :
    ∑' y, ssrw1 x y * g y = 2⁻¹ * g (x + 1) + 2⁻¹ * g (x - 1) := by
  rw [tsum_eq_sum (s := {x + 1, x - 1}) (fun y hy => ?_), Finset.sum_pair (by omega)]
  · simp only [ssrw1, show x + 1 - x = 1 ∨ x + 1 - x = -1 from Or.inl (by ring),
      show x - 1 - x = 1 ∨ x - 1 - x = -1 from Or.inr (by ring), ↓reduceIte]
  · rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    simp only [ssrw1, show ¬ (y - x = 1 ∨ y - x = -1) by omega, ↓reduceIte, zero_mul]

/-- The walk is a transition matrix. -/
theorem isTransitionMatrix_ssrw1 : IsTransitionMatrix ssrw1 := fun x => by
  have := tsum_ssrw1_mul x 1
  simp only [Pi.one_apply, mul_one] at this
  rw [this, ENNReal.inv_two_add_inv_two]

/-- The number of paths: `cnt n d = Σ_k 1{2k − n = d} C(n, k)`, the number of `±1` paths of
length `n` with displacement `d`. -/
noncomputable def ssrwCount (n : ℕ) (d : ℤ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (n + 1), if 2 * (k : ℤ) - n = d then (n.choose k : ℝ≥0∞) else 0

/-- Pascal's rule for the path counts: `cnt(n + 1, d) = cnt(n, d − 1) + cnt(n, d + 1)`. -/
theorem ssrwCount_succ (n : ℕ) (d : ℤ) :
    ssrwCount (n + 1) d = ssrwCount n (d - 1) + ssrwCount n (d + 1) := by
  have hA : ∀ k : ℕ, (if 2 * ((k + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = d then
      ((n + 1).choose (k + 1) : ℝ≥0∞) else 0) =
      (if 2 * (k : ℤ) - n = d - 1 then (n.choose k : ℝ≥0∞) else 0) +
      (if 2 * ((k + 1 : ℕ) : ℤ) - n = d + 1 then (n.choose (k + 1) : ℝ≥0∞) else 0) :=
    fun k => by
      rw [Nat.choose_succ_succ', Nat.cast_add (R := ℝ≥0∞)]
      by_cases h : 2 * ((k + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = d
      · have h1 : 2 * (k : ℤ) - n = d - 1 := by push_cast at h; omega
        have h2 : 2 * ((k + 1 : ℕ) : ℤ) - n = d + 1 := by push_cast at h ⊢; omega
        simp only [h, h1, h2, ↓reduceIte]
      · have h1 : ¬ 2 * (k : ℤ) - n = d - 1 := by push_cast at h; omega
        have h2 : ¬ 2 * ((k + 1 : ℕ) : ℤ) - n = d + 1 := by push_cast at h ⊢; omega
        simp only [h, h1, h2, ↓reduceIte, add_zero]
  have h0 : (if 2 * ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = d then
      ((n + 1).choose 0 : ℝ≥0∞) else 0) =
      (if 2 * ((0 : ℕ) : ℤ) - n = d + 1 then (n.choose 0 : ℝ≥0∞) else 0) := by
    rw [Nat.choose_zero_right, Nat.choose_zero_right]
    by_cases h : 2 * ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = d
    · have h2 : 2 * ((0 : ℕ) : ℤ) - n = d + 1 := by push_cast at h ⊢; omega
      simp only [h, h2, ↓reduceIte]
    · have h2 : ¬ 2 * ((0 : ℕ) : ℤ) - n = d + 1 := by push_cast at h ⊢; omega
      simp only [h, h2, ↓reduceIte]
  unfold ssrwCount
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp_rw [hA]
  rw [Finset.sum_add_distrib, h0,
    Finset.sum_range_succ (fun k => if 2 * ((k + 1 : ℕ) : ℤ) - n = d + 1 then
      (n.choose (k + 1) : ℝ≥0∞) else 0) n, Nat.choose_succ_self, Nat.cast_zero, ite_self,
    add_zero, Finset.sum_range_succ' (fun k => if 2 * (k : ℤ) - n = d + 1 then
      (n.choose k : ℝ≥0∞) else 0) n]
  ring

/-- **The `n`-step probabilities of the walk**: `Pⁿ(x, z) = 2⁻ⁿ cnt(n, z − x)`. -/
theorem matPow_ssrw1 (n : ℕ) (x z : ℤ) : matPow ssrw1 n x z = 2⁻¹ ^ n * ssrwCount n (z - x) := by
  induction n generalizing x with
  | zero =>
    simp only [matPow, ssrwCount, zero_add, Finset.sum_range_one, Nat.choose_self,
      Nat.cast_one, pow_zero, one_mul, CharP.cast_eq_zero, mul_zero, sub_zero]
    by_cases h : x = z
    · simp [h]
    · simp [h, show (0 : ℤ) ≠ z - x by omega]
  | succ n ih =>
    simp only [matPow]
    rw [tsum_ssrw1_mul, ih, ih, ssrwCount_succ, show z - (x + 1) = z - x - 1 by ring,
      show z - (x - 1) = z - x + 1 by ring, pow_succ]
    ring

/-- **(MT p. 464, via Spitzer)**: `P²ⁿ(x, x) = C(2n, n)/4ⁿ` for the simple random walk. -/
theorem matPow_ssrw1_even (n : ℕ) (x : ℤ) :
    matPow ssrw1 (2 * n) x x = (Nat.centralBinom n : ℝ≥0∞) / 4 ^ n := by
  rw [matPow_ssrw1, sub_self, ssrwCount, Finset.sum_eq_single n (fun k _ hk => ?_)
    (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
  · simp only [show 2 * (n : ℤ) - ((2 * n : ℕ) : ℤ) = 0 by push_cast; ring, ↓reduceIte]
    rw [← Nat.centralBinom_eq_two_mul_choose, div_eq_mul_inv, mul_comm, pow_mul,
      ← ENNReal.inv_pow, ← ENNReal.inv_pow]
    norm_num
  · have : ¬ 2 * (k : ℤ) - ((2 * n : ℕ) : ℤ) = 0 := by push_cast; omega
    simp only [this, ↓reduceIte]

/-- The walk has period two: `P²ⁿ⁺¹(x, x) = 0`. -/
theorem matPow_ssrw1_odd (n : ℕ) (x : ℤ) : matPow ssrw1 (2 * n + 1) x x = 0 := by
  rw [matPow_ssrw1, sub_self, ssrwCount, Finset.sum_eq_zero fun k _ => ?_, mul_zero]
  have : ¬ 2 * (k : ℤ) - ((2 * n + 1 : ℕ) : ℤ) = 0 := by push_cast; omega
  simp only [this, ↓reduceIte]

/-! ### The simple symmetric random walk on `ℤ²` and the 45° rotation -/

/-- The simple symmetric random walk on `ℤ²`: a step to each of the four neighbours with
probability `¼`. -/
noncomputable def ssrw2 (u v : ℤ × ℤ) : ℝ≥0∞ :=
  if (v.1 - u.1 = 1 ∧ v.2 - u.2 = 0) ∨ (v.1 - u.1 = -1 ∧ v.2 - u.2 = 0) ∨
      (v.1 - u.1 = 0 ∧ v.2 - u.2 = 1) ∨ (v.1 - u.1 = 0 ∧ v.2 - u.2 = -1) then 4⁻¹ else 0

/-- The 45° rotation `(a, b) ↦ (a + b, a − b)` of `ℤ²` onto the even sublattice. -/
def rot (u : ℤ × ℤ) : ℤ × ℤ := (u.1 + u.2, u.1 - u.2)

/-- The rotation is injective. -/
theorem rot_injective : Function.Injective rot := fun u v h => by
  simp only [rot, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

/-- **The rotation turns the walk on `ℤ²` into two independent walks on `ℤ`**: one step of the
`ℤ²` walk is a step `(±1, ±1)` of the rotated walk, with independent signs. -/
theorem ssrw2_eq_prodMat (u v : ℤ × ℤ) : ssrw2 u v = prodMat ssrw1 ssrw1 (rot u) (rot v) := by
  have h4 : (4⁻¹ : ℝ≥0∞) = 2⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]; norm_num
  simp only [ssrw2, prodMat, ssrw1, rot]
  by_cases h1 : v.1 + v.2 - (u.1 + u.2) = 1 ∨ v.1 + v.2 - (u.1 + u.2) = -1 <;>
  by_cases h2 : v.1 - v.2 - (u.1 - u.2) = 1 ∨ v.1 - v.2 - (u.1 - u.2) = -1 <;>
  by_cases h : (v.1 - u.1 = 1 ∧ v.2 - u.2 = 0) ∨ (v.1 - u.1 = -1 ∧ v.2 - u.2 = 0) ∨
      (v.1 - u.1 = 0 ∧ v.2 - u.2 = 1) ∨ (v.1 - u.1 = 0 ∧ v.2 - u.2 = -1) <;>
  simp only [h, h1, h2, ↓reduceIte] <;>
  first | exact h4 | (exfalso; omega) | rw [mul_zero] | rw [zero_mul]

/-- From the even sublattice the rotated walk stays in it. -/
theorem prodMat_ssrw1_rot_support (u w : ℤ × ℤ) (h : prodMat ssrw1 ssrw1 (rot u) w ≠ 0) :
    w ∈ range rot := by
  simp only [prodMat, ssrw1, rot] at h
  by_cases h1 : w.1 - (u.1 + u.2) = 1 ∨ w.1 - (u.1 + u.2) = -1
  · by_cases h2 : w.2 - (u.1 - u.2) = 1 ∨ w.2 - (u.1 - u.2) = -1
    · refine ⟨((w.1 + w.2) / 2, (w.1 - w.2) / 2), Prod.ext ?_ ?_⟩ <;> simp only [rot] <;> omega
    · simp only [h2, ↓reduceIte, mul_zero, ne_eq, not_true_eq_false] at h
  · simp only [h1, ↓reduceIte, zero_mul, ne_eq, not_true_eq_false] at h

/-- **The `ℤ²` walk is the rotated product walk**: `Pⁿ_{ℤ²}(u, v) = Pⁿ_{ℤ}((Ru)₁, (Rv)₁)
Pⁿ_{ℤ}((Ru)₂, (Rv)₂)`. -/
theorem matPow_ssrw2 (n : ℕ) (u v : ℤ × ℤ) :
    matPow ssrw2 n u v = matPow ssrw1 n (rot u).1 (rot v).1 * matPow ssrw1 n (rot u).2 (rot v).2 :=
  (matPow_eq_of_injective rot_injective ssrw2_eq_prodMat prodMat_ssrw1_rot_support n u v).trans
    (matPow_prodMat _ _ n _ _)

/-- The `ℤ²` walk is a transition matrix. -/
theorem isTransitionMatrix_ssrw2 : IsTransitionMatrix ssrw2 := fun u => by
  simp_rw [ssrw2_eq_prodMat]
  rw [rot_injective.tsum_eq (f := fun w => prodMat ssrw1 ssrw1 (rot u) w)
    (fun w hw => prodMat_ssrw1_rot_support u w hw)]
  exact isTransitionMatrix_prodMat isTransitionMatrix_ssrw1 isTransitionMatrix_ssrw1 (rot u)

/-- `P²ⁿ_{ℤ²}(u, u) = c_n²` with `c_n = C(2n, n)/4ⁿ`. -/
theorem matPow_ssrw2_even (n : ℕ) (u : ℤ × ℤ) :
    matPow ssrw2 (2 * n) u u = ((Nat.centralBinom n : ℝ≥0∞) / 4 ^ n) ^ 2 := by
  rw [matPow_ssrw2, matPow_ssrw1_even, matPow_ssrw1_even, sq]

/-- `P²ⁿ⁺¹_{ℤ²}(u, u) = 0`. -/
theorem matPow_ssrw2_odd (n : ℕ) (u : ℤ × ℤ) : matPow ssrw2 (2 * n + 1) u u = 0 := by
  rw [matPow_ssrw2, matPow_ssrw1_odd, zero_mul]

/-! ### Two independent copies of the `ℤ²` walk: a walk on `ℤ⁴` -/

/-- Two independent copies of the walk on `ℤ²`, a random walk on `ℤ⁴ = ℤ² × ℤ²`. -/
noncomputable def ssrw4 : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) → ℝ≥0∞ := prodMat ssrw2 ssrw2

/-- `ssrw4` is a transition matrix. -/
theorem isTransitionMatrix_ssrw4 : IsTransitionMatrix ssrw4 :=
  isTransitionMatrix_prodMat isTransitionMatrix_ssrw2 isTransitionMatrix_ssrw2

/-- `P²ⁿ_{ℤ⁴}(w, w) = c_n⁴`. -/
theorem matPow_ssrw4_even (n : ℕ) (w : (ℤ × ℤ) × (ℤ × ℤ)) :
    matPow ssrw4 (2 * n) w w = ((Nat.centralBinom n : ℝ≥0∞) / 4 ^ n) ^ 4 := by
  rw [ssrw4, matPow_prodMat, matPow_ssrw2_even, matPow_ssrw2_even, ← pow_add]

/-- `P²ⁿ⁺¹_{ℤ⁴}(w, w) = 0`. -/
theorem matPow_ssrw4_odd (n : ℕ) (w : (ℤ × ℤ) × (ℤ × ℤ)) :
    matPow ssrw4 (2 * n + 1) w w = 0 := by
  rw [ssrw4, matPow_prodMat, matPow_ssrw2_odd, zero_mul]

/-! ### The bounds `1/(4n) ≤ c_n² ≤ 1/(2n + 1)` -/

/-- `c_n = C(2n, n)/4ⁿ`, the return probability `P²ⁿ(0, 0)` of the walk on `ℤ`. -/
noncomputable def centralC (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

/-- `c_n ≥ 0`. -/
theorem centralC_nonneg (n : ℕ) : 0 ≤ centralC n := by unfold centralC; positivity

/-- `c_{n+1} = c_n (2n + 1)/(2n + 2)`. -/
theorem centralC_succ (n : ℕ) :
    centralC (n + 1) = centralC n * ((2 * n + 1) / (2 * n + 2)) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hR : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h
  have hC : (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) := by
    rw [eq_div_iff (by positivity)]
    linarith
  unfold centralC
  rw [hC, pow_succ]
  field_simp
  ring

/-- `c_n² ≤ 1/(2n + 1)`, since `((2k+1)/(2k+2))² ≤ (2k+1)/(2k+3)` telescopes. -/
theorem centralC_sq_le (n : ℕ) : centralC n ^ 2 ≤ 1 / (2 * n + 1) := by
  induction n with
  | zero => simp [centralC]
  | succ n ih =>
    rw [centralC_succ, mul_pow]
    have h0 : (0 : ℝ) ≤ ((2 * n + 1) / (2 * n + 2)) ^ 2 := by positivity
    calc centralC n ^ 2 * ((2 * n + 1) / (2 * n + 2)) ^ 2
        ≤ 1 / (2 * n + 1) * ((2 * n + 1) / (2 * n + 2)) ^ 2 := mul_le_mul_of_nonneg_right ih h0
      _ ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [div_mul_eq_mul_div, one_mul, div_pow, div_div, div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith

/-- `c_{n+1}² ≥ 1/(4(n + 1))`, since `((2k+1)/(2k+2))² ≥ k/(k+1)` telescopes. -/
theorem centralC_sq_ge (n : ℕ) : 1 / (4 * ((n : ℝ) + 1)) ≤ centralC (n + 1) ^ 2 := by
  induction n with
  | zero =>
    rw [centralC_succ]
    simp [centralC]
    norm_num
  | succ n ih =>
    rw [centralC_succ (n + 1), mul_pow]
    have h0 : (0 : ℝ) ≤ ((2 * ((n + 1 : ℕ) : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 2)) ^ 2 := by
      positivity
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih h0)
    push_cast
    rw [div_mul_eq_mul_div, one_mul, div_pow, div_div, div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith

/-- `C(2n, n)/4ⁿ = c_n` in `[0, ∞]`. -/
theorem centralBinom_div_eq_ofReal (n : ℕ) :
    (Nat.centralBinom n : ℝ≥0∞) / 4 ^ n = ENNReal.ofReal (centralC n) := by
  rw [centralC, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- `Σₙ 1/(4(n + 1)) = ∞`. -/
theorem tsum_ofReal_inv_four_succ :
    ∑' n : ℕ, ENNReal.ofReal (1 / (4 * ((n : ℝ) + 1))) = ∞ := by
  by_contra h
  have hs : Summable fun n : ℕ => 1 / (4 * ((n : ℝ) + 1)) :=
    (ENNReal.summable_toReal h).congr fun n => ENNReal.toReal_ofReal (by positivity)
  have h2 : Summable fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) :=
    (hs.mul_left 4).congr fun n => by push_cast; field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h2)

/-! ### Recurrence in two dimensions, transience in four -/

/-- The walk on `ℤ²` is recurrent (MT p. 464, Pólya): `U(u, u) = Σₙ Pⁿ(u, u) = ∞`, since
`P²ⁿ(u, u) = c_n² ≥ 1/(4n)`. -/
theorem ssrw2_isRecurrentState (u : ℤ × ℤ) :
    haveI := isMarkovKernel_matKernel isTransitionMatrix_ssrw2
    IsRecurrentState (matKernel ssrw2) u := by
  have := isMarkovKernel_matKernel isTransitionMatrix_ssrw2
  unfold IsRecurrentState
  rw [potKernel_apply _ _ (measurableSet_singleton u)]
  simp_rw [matKernel_pow_singleton]
  refine top_unique (tsum_ofReal_inv_four_succ.symm.le.trans ?_)
  refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => 2 * n + 1)
    (fun a b h => by have : 2 * a + 1 = 2 * b + 1 := h; omega)
    (fun n => matPow ssrw2 (n + 1) u u))
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, matPow_ssrw2_even, centralBinom_div_eq_ofReal,
    ← ENNReal.ofReal_pow (centralC_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (centralC_sq_ge n)

/-- The walk on `ℤ⁴` made of two independent walks on `ℤ²` is transient:
`U(w, w) = Σₙ Pⁿ(w, w) < ∞`, since `P²ⁿ(w, w) = c_n⁴ ≤ 1/(2n + 1)²`. -/
theorem ssrw4_isTransientState (w : (ℤ × ℤ) × (ℤ × ℤ)) :
    haveI := isMarkovKernel_matKernel isTransitionMatrix_ssrw4
    IsTransientState (matKernel ssrw4) w := by
  have := isMarkovKernel_matKernel isTransitionMatrix_ssrw4
  unfold IsTransientState
  rw [potKernel_apply _ _ (measurableSet_singleton w)]
  simp_rw [matKernel_pow_singleton]
  set f : ℕ → ℝ≥0∞ := fun n => matPow ssrw4 n w w with hf
  have hshift : ∑' n, f (n + 1) ≤ ∑' n, f n := by
    rw [tsum_eq_zero_add' ENNReal.summable (f := f)]
    exact le_add_self
  have hsplit : ∑' n, f n = ∑' k, f (2 * k) + ∑' k, f (2 * k + 1) :=
    (tsum_even_add_odd ENNReal.summable ENNReal.summable).symm
  have hodd : ∑' k, f (2 * k + 1) = 0 :=
    ENNReal.tsum_eq_zero.2 fun k => matPow_ssrw4_odd k w
  have hb : ∀ n : ℕ, centralC n ^ 4 ≤ 1 / ((n : ℝ) + 1) ^ 2 := fun n => by
    have h1 : centralC n ^ 4 ≤ (1 / (2 * (n : ℝ) + 1)) ^ 2 := by
      rw [show centralC n ^ 4 = (centralC n ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) (centralC_sq_le n) 2
    refine h1.trans ?_
    rw [div_pow, one_pow]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hsum : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 ((Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two)
    exact this.congr fun n => by push_cast; ring
  have heven : ∑' k, f (2 * k) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum
      (g := fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2)) fun k => ?_)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
      exact ENNReal.ofReal_ne_top
    · change matPow ssrw4 (2 * k) w w ≤ _
      rw [matPow_ssrw4_even, centralBinom_div_eq_ofReal, ← ENNReal.ofReal_pow (centralC_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hb k)
  refine ne_top_of_le_ne_top ?_ hshift
  rw [hsplit, hodd, add_zero]
  exact heven

/-! ### Independent copies and the coupling time -/

/-- **`ssrw4` is the chain of two independent copies of the `ℤ²` walk**: its transition law from
`(x, y)` is the product `P(x, ·) ⊗ P(y, ·)`. -/
theorem matKernel_ssrw4 (x y : ℤ × ℤ) :
    matKernel ssrw4 (x, y) = (matKernel ssrw2 x).prod (matKernel ssrw2 y) := by
  have := isMarkovKernel_matKernel isTransitionMatrix_ssrw2
  refine Measure.ext_of_singleton fun z => ?_
  rw [matKernel_singleton, ← singleton_prod_singleton, Measure.prod_prod, matKernel_singleton,
    matKernel_singleton]
  rfl

/-- The `n`-step probabilities of the two copies multiply:
`Pⁿ((x, y), {(a, b)}) = Pⁿ(x, {a}) Pⁿ(y, {b})`. -/
theorem matKernel_ssrw4_pow (n : ℕ) (x y a b : ℤ × ℤ) :
    (matKernel ssrw4 ^ n) (x, y) {(a, b)} =
      (matKernel ssrw2 ^ n) x {a} * (matKernel ssrw2 ^ n) y {b} := by
  rw [matKernel_pow_singleton, matKernel_pow_singleton, matKernel_pow_singleton, ssrw4,
    matPow_prodMat]

/-- **The coupling of independent copies fails** (MT p. 464). The return times to `u` of the
`ℤ²` walk form a proper renewal process: `L(u, u) = 1`. But two independent copies started
together at `u` have a joint renewal (both back at `u` at the same time `n ≥ 1`) exactly when
the chain `ssrw4` returns to `(u, u)`, and this happens with probability `L((u, u), (u, u)) < 1`:
the joint renewal time, the coupling time of §13.2, is infinite with positive probability. -/
theorem independent_coupling_fails (u : ℤ × ℤ) :
    haveI := isMarkovKernel_matKernel isTransitionMatrix_ssrw2
    haveI := isMarkovKernel_matKernel isTransitionMatrix_ssrw4
    hitProb (matKernel ssrw2) {u} u = 1 ∧ hitProb (matKernel ssrw4) {(u, u)} (u, u) < 1 := by
  have := isMarkovKernel_matKernel isTransitionMatrix_ssrw2
  have := isMarkovKernel_matKernel isTransitionMatrix_ssrw4
  refine ⟨(proposition_8_1_3 _ u).1 (ssrw2_isRecurrentState u),
    lt_of_le_of_ne (hitProb_le_one _ _ _) fun h => ?_⟩
  exact ssrw4_isTransientState (u, u) ((proposition_8_1_3 _ (u, u)).2 h)

end MeynTweedie.Positivity

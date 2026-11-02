/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleDefs

/-!
# The base-`b` Haar decomposition and the second moment of a scrambled sum (Owen 1997)

Owen (1997) computes the variance of scrambled net quadrature through the base-`b` Haar
(multiresolution) ANOVA decomposition of the integrand. On the digit grid
`Fin s → Fin D → Fin b` this is finite linear algebra with kernels:

* `agreeKernel r` (`K_r`): average over the level-`r` cell; `sum_agreeKernel_mul`:
  `K_r K_{r'} = K_{min(r,r')}`; `agreeKernel_self_depth`: `K_D` is the identity.
* `detailKernel ℓ` (`δ_0 = K_0`, `δ_{ℓ+1} = K_{ℓ+1} - K_ℓ`): symmetric (`detailKernel_comm`),
  idempotent (`sum_detailKernel_mul`), telescoping to `K_r` (`sum_range_detailKernel`).
* `haarKernel ℓ = Π_j δ_{ℓ_j}` for `ℓ : Fin s → Fin (D + 1)`: symmetric, idempotent, summing to
  the identity (`sum_haarKernel`); hence the variance components
  `haarVar F ℓ = b^{-sD} Σ_{y,z} F(y) H_ℓ(y,z) F(z)` are sums of squares (`qform_eq_sum_sq`,
  `haarVar_nonneg`), add up to the mean square (`sum_haarVar`, Parseval), and `haarVar F 0` is
  the squared mean (`haarVar_zero`).
* `gainWeight b k ℓ` (`1` for `ℓ ≤ k`, `-1/(b-1)` for `ℓ = k+1`, `0` beyond) and
  `pairKernel_eq_sum`, `prod_pairKernel_eq_sum`: the pair law of two scrambled points with
  `k_j` common digits in coordinate `j` is `b^{-sD} Σ_ℓ (Π_j w(k_j, ℓ_j)) H_ℓ`.
* `scrambleVec`, `card_scrambleVec_pair` (**`s`-dimensional pair law**, item (iii)),
  `card_scrambleVec`, `sum_scrambleVec`, `sum_scrambleVec_pair`.
* `gainCoeff b d ℓ = n⁻¹ Σ_{i,i'} Π_j w(k_j(i,i'), ℓ_j)`: Owen's gain coefficients of a point
  set; `gainCoeff_zero`: `Γ_0 = n`.
* `sum_sq_sum_scrambleVec` (**the key identity**): averaging over the scrambles,
  `E[(Σ_i F(σ d_i))²] = n Σ_ℓ Γ_ℓ σ²_ℓ(F)`, for every function `F` on the grid and every point
  set `d`.
-/

namespace RQMCMarkov.OwenScrambling

open Finset

variable {b D : ℕ}

/-- Composition of averaging kernels, `r ≤ r'`. -/
theorem sum_agreeKernel_mul_of_le (hb : 0 < b) {r r' : ℕ} (h : r ≤ r') (x z : Fin D → Fin b) :
    ∑ y, agreeKernel r x y * agreeKernel r' y z = agreeKernel r x z := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have key : ∀ y, agreeKernel r x y * agreeKernel r' y z =
      if Agree r' z y then agreeKernel r x z * ((b : ℝ) ^ min r' D / (b : ℝ) ^ D) else 0 := by
    intro y
    unfold agreeKernel
    by_cases h1 : Agree r' z y
    · have h1' : Agree r' y z := agree_symm h1
      have hyz : Agree r y z := agree_mono h h1'
      rw [ite_eq_left h1', ite_eq_left h1]
      by_cases h2 : Agree r x y
      · rw [ite_eq_left h2, ite_eq_left (agree_trans h2 hyz)]
      · have h3 : ¬ Agree r x z := fun h3 ↦ h2 (agree_trans h3 (agree_symm hyz))
        rw [ite_eq_right h2, ite_eq_right h3, zero_mul]
    · have h1' : ¬ Agree r' y z := fun h' ↦ h1 (agree_symm h')
      rw [ite_eq_right h1', ite_eq_right h1, mul_zero]
  rw [Finset.sum_congr rfl (fun y _ ↦ key y), ← Finset.sum_filter, Finset.sum_const,
    card_agree hb, nsmul_eq_mul, Nat.cast_pow]
  have hp : (b : ℝ) ^ (D - min r' D) * (b : ℝ) ^ min r' D = (b : ℝ) ^ D := by
    rw [← pow_add, Nat.sub_add_cancel (min_le_right _ _)]
  rw [show (b : ℝ) ^ (D - min r' D) * (agreeKernel r x z * ((b : ℝ) ^ min r' D / (b : ℝ) ^ D)) =
      agreeKernel r x z * (((b : ℝ) ^ (D - min r' D) * (b : ℝ) ^ min r' D) / (b : ℝ) ^ D) by ring,
    hp, div_self (pow_pos hb' D).ne', mul_one]

/-- **Composition of averaging kernels**: `K_r K_{r'} = K_{min(r, r')}` (the cell averages
form a nested family of commuting projections). -/
theorem sum_agreeKernel_mul (hb : 0 < b) (r r' : ℕ) (x z : Fin D → Fin b) :
    ∑ y, agreeKernel r x y * agreeKernel r' y z = agreeKernel (min r r') x z := by
  rcases le_total r r' with h | h
  · rw [min_eq_left h]
    exact sum_agreeKernel_mul_of_le hb h x z
  · rw [min_eq_right h]
    calc ∑ y, agreeKernel r x y * agreeKernel r' y z
        = ∑ y, agreeKernel r' z y * agreeKernel r y x := by
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [agreeKernel_comm r x y, agreeKernel_comm r' y z, mul_comm]
      _ = agreeKernel r' z x := sum_agreeKernel_mul_of_le hb h z x
      _ = agreeKernel r' x z := agreeKernel_comm r' z x

/-- The averaging kernel at depth `D` is the identity. -/
theorem agreeKernel_self_depth (hb : 0 < b) (x y : Fin D → Fin b) :
    agreeKernel D x y = if x = y then 1 else 0 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  unfold agreeKernel
  rw [min_self]
  by_cases h : x = y
  · rw [ite_eq_left ((agree_iff_eq le_rfl).2 h), ite_eq_left h, div_self (pow_pos hb' D).ne']
  · rw [ite_eq_right fun h' ↦ h ((agree_iff_eq le_rfl).1 h'), ite_eq_right h]

/-- The averaging kernel at level `0` is the constant `b^{-D}`. -/
theorem agreeKernel_zero (x y : Fin D → Fin b) :
    agreeKernel 0 x y = 1 / (b : ℝ) ^ D := by
  unfold agreeKernel
  rw [ite_eq_left fun l hl ↦ absurd hl (Nat.not_lt_zero _), Nat.zero_min, pow_zero]

/-- The level-`r` kernel only sees the first `min r D` digits. -/
theorem agreeKernel_min (r : ℕ) (x y : Fin D → Fin b) :
    agreeKernel (min r D) x y = agreeKernel r x y := by
  unfold agreeKernel
  rw [min_assoc, min_self]
  by_cases h : Agree r x y
  · rw [ite_eq_left ((agree_min_iff r x y).2 h), ite_eq_left h]
  · rw [ite_eq_right fun h' ↦ h ((agree_min_iff r x y).1 h'), ite_eq_right h]

/-- The **detail kernel** at level `ℓ`: `δ_0 = K_0` (the mean) and `δ_{ℓ+1} = K_{ℓ+1} - K_ℓ`
(the base-`b` Haar detail between resolutions `ℓ` and `ℓ + 1`). -/
noncomputable def detailKernel : ℕ → (Fin D → Fin b) → (Fin D → Fin b) → ℝ
  | 0 => agreeKernel 0
  | ℓ + 1 => fun x y ↦ agreeKernel (ℓ + 1) x y - agreeKernel ℓ x y

/-- The detail kernels are symmetric. -/
theorem detailKernel_comm (ℓ : ℕ) (x y : Fin D → Fin b) :
    detailKernel ℓ x y = detailKernel ℓ y x := by
  cases ℓ with
  | zero => exact agreeKernel_comm 0 x y
  | succ ℓ =>
    change agreeKernel (ℓ + 1) x y - agreeKernel ℓ x y = agreeKernel (ℓ + 1) y x - agreeKernel ℓ y x
    rw [agreeKernel_comm (ℓ + 1) x y, agreeKernel_comm ℓ x y]

/-- The detail kernels are idempotent: `δ_ℓ δ_ℓ = δ_ℓ`. -/
theorem sum_detailKernel_mul (hb : 0 < b) (ℓ : ℕ) (x z : Fin D → Fin b) :
    ∑ y, detailKernel ℓ x y * detailKernel ℓ y z = detailKernel ℓ x z := by
  cases ℓ with
  | zero =>
    change ∑ y, agreeKernel 0 x y * agreeKernel 0 y z = agreeKernel 0 x z
    rw [sum_agreeKernel_mul hb, min_self]
  | succ ℓ =>
    change ∑ y, (agreeKernel (ℓ + 1) x y - agreeKernel ℓ x y) *
      (agreeKernel (ℓ + 1) y z - agreeKernel ℓ y z) = agreeKernel (ℓ + 1) x z - agreeKernel ℓ x z
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, sum_agreeKernel_mul hb, min_self,
      min_eq_right (Nat.le_succ ℓ), min_eq_left (Nat.le_succ ℓ)]
    ring

/-- **Telescoping**: `K_r = Σ_{ℓ ≤ r} δ_ℓ`. -/
theorem sum_range_detailKernel (r : ℕ) (x y : Fin D → Fin b) :
    ∑ ℓ ∈ Finset.range (r + 1), detailKernel ℓ x y = agreeKernel r x y := by
  induction r with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    change agreeKernel r x y + (agreeKernel (r + 1) x y - agreeKernel r x y) = _
    ring

/-- `K_r = Σ_{ℓ ≤ D, ℓ ≤ r} δ_ℓ`, as a sum over `Fin (D + 1)`. -/
theorem agreeKernel_eq_sum_fin (r : ℕ) (x y : Fin D → Fin b) :
    agreeKernel r x y =
      ∑ ℓ : Fin (D + 1), if (ℓ : ℕ) ≤ r then detailKernel ℓ x y else 0 := by
  rw [← agreeKernel_min, ← sum_range_detailKernel, Fin.sum_univ_eq_sum_range
    (fun ℓ ↦ if ℓ ≤ r then detailKernel ℓ x y else 0), ← Finset.sum_filter]
  congr 1
  ext ℓ
  rw [Finset.mem_range, Finset.mem_filter, Finset.mem_range]
  omega

/-- The **gain weight** of a detail level `ℓ` for a pair with `k` common digits:
`(b [ℓ ≤ k] - [ℓ ≤ k + 1]) / (b - 1)`, i.e. `1` for `ℓ ≤ k`, `-1/(b-1)` for `ℓ = k + 1` and `0`
beyond (Owen 1997). -/
noncomputable def gainWeight (b : ℕ) (k ℓ : ℕ) : ℝ :=
  ((b : ℝ) * (if ℓ ≤ k then 1 else 0) - (if ℓ ≤ k + 1 then 1 else 0)) / ((b : ℝ) - 1)

/-- The gain weight of the mean (`ℓ = 0`) is `1`. -/
theorem gainWeight_zero (hb : 1 < b) (k : ℕ) : gainWeight b k 0 = 1 := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  unfold gainWeight
  rw [ite_eq_left (Nat.zero_le k), ite_eq_left (Nat.zero_le _), mul_one, div_self hb1]

/-- **The pair kernel in the Haar basis**: `π_k = b^{-D} Σ_ℓ w(k, ℓ) δ_ℓ`. -/
theorem pairKernel_eq_sum (hb : 1 < b) (k : ℕ) (x y : Fin D → Fin b) :
    pairKernel k x y =
      (∑ ℓ : Fin (D + 1), gainWeight b k ℓ * detailKernel ℓ x y) / (b : ℝ) ^ D := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  unfold pairKernel gainWeight
  rw [agreeKernel_eq_sum_fin k, agreeKernel_eq_sum_fin (k + 1), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  split_ifs <;> field_simp <;> ring

/-- The `s`-dimensional Haar kernel `Π_j δ_{ℓ_j}` of the multiresolution component `ℓ`. -/
noncomputable def haarKernel {s : ℕ} (ℓ : Fin s → Fin (D + 1)) (y z : Fin s → Fin D → Fin b) :
    ℝ :=
  ∏ j, detailKernel (ℓ j) (y j) (z j)

/-- Products of coordinatewise kernels compose coordinatewise. -/
theorem sum_prod_mul_prod {s : ℕ} {X : Type*} [Fintype X] (A B : Fin s → X → X → ℝ)
    (y w : Fin s → X) :
    ∑ z : Fin s → X, (∏ j, A j (y j) (z j)) * ∏ j, B j (z j) (w j) =
      ∏ j, ∑ x, A j (y j) x * B j x (w j) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Finset.prod_mul_distrib]

/-- The Haar kernels are symmetric. -/
theorem haarKernel_comm {s : ℕ} (ℓ : Fin s → Fin (D + 1)) (y z : Fin s → Fin D → Fin b) :
    haarKernel ℓ y z = haarKernel ℓ z y :=
  Finset.prod_congr rfl fun _ _ ↦ detailKernel_comm _ _ _

/-- The Haar kernels are idempotent. -/
theorem sum_haarKernel_mul (hb : 0 < b) {s : ℕ} (ℓ : Fin s → Fin (D + 1))
    (y w : Fin s → Fin D → Fin b) :
    ∑ z, haarKernel ℓ y z * haarKernel ℓ z w = haarKernel ℓ y w := by
  unfold haarKernel
  rw [sum_prod_mul_prod (fun j ↦ detailKernel (ℓ j : ℕ)) (fun j ↦ detailKernel (ℓ j : ℕ))]
  exact Finset.prod_congr rfl fun _ _ ↦ sum_detailKernel_mul hb _ _ _

/-- The quadratic form `Σ_{y,z} F(y) K(y,z) F(z)` of a kernel. -/
noncomputable def qform {G : Type*} [Fintype G] (K : G → G → ℝ) (F : G → ℝ) : ℝ :=
  ∑ y, ∑ z, F y * K y z * F z

/-- The quadratic form of a symmetric idempotent kernel is a sum of squares. -/
theorem qform_eq_sum_sq {G : Type*} [Fintype G] {K : G → G → ℝ}
    (hsymm : ∀ y z, K y z = K z y) (hidem : ∀ y w, ∑ z, K y z * K z w = K y w) (F : G → ℝ) :
    qform K F = ∑ z, (∑ y, F y * K y z) ^ 2 := by
  unfold qform
  have e1 : ∀ z, (∑ y, F y * K y z) ^ 2 = ∑ y, ∑ w, F y * K y z * (F w * K w z) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
  calc ∑ y, ∑ w, F y * K y w * F w = ∑ y, ∑ w, ∑ z, F y * K y z * (F w * K w z) := by
        refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
        rw [← hidem y w, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [hsymm z w]
        ring
    _ = ∑ y, ∑ z, ∑ w, F y * K y z * (F w * K w z) :=
        Finset.sum_congr rfl fun y _ ↦ Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ w, F y * K y z * (F w * K w z) := Finset.sum_comm
    _ = ∑ z, (∑ y, F y * K y z) ^ 2 := Finset.sum_congr rfl fun z _ ↦ (e1 z).symm

/-- **Nonnegativity of the variance components**: `σ²_ℓ ≥ 0`. -/
theorem qform_haarKernel_nonneg (hb : 0 < b) {s : ℕ} (ℓ : Fin s → Fin (D + 1))
    (F : (Fin s → Fin D → Fin b) → ℝ) : 0 ≤ qform (haarKernel ℓ) F := by
  rw [qform_eq_sum_sq (haarKernel_comm ℓ) (sum_haarKernel_mul hb ℓ)]
  exact Finset.sum_nonneg fun z _ ↦ sq_nonneg _

/-- The Haar kernels sum to the identity. -/
theorem sum_haarKernel (hb : 0 < b) {s : ℕ} (y z : Fin s → Fin D → Fin b) :
    ∑ ℓ : Fin s → Fin (D + 1), haarKernel ℓ y z = if y = z then 1 else 0 := by
  unfold haarKernel
  rw [← Fintype.prod_sum (fun j (ℓ : Fin (D + 1)) ↦ detailKernel (ℓ : ℕ) (y j) (z j))]
  have h1 : ∀ j, ∑ ℓ : Fin (D + 1), detailKernel (ℓ : ℕ) (y j) (z j) =
      if y j = z j then 1 else 0 := by
    intro j
    rw [Fin.sum_univ_eq_sum_range (fun ℓ ↦ detailKernel ℓ (y j) (z j)), sum_range_detailKernel,
      agreeKernel_self_depth hb]
  rw [Finset.prod_congr rfl fun j _ ↦ h1 j]
  by_cases h : y = z
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun j _ ↦ ite_eq_left (congrFun h j)
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ z j := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- The Haar kernel of the mean (`ℓ = 0`) is the constant `b^{-sD}`. -/
theorem haarKernel_zero {s : ℕ} (y z : Fin s → Fin D → Fin b) :
    haarKernel (0 : Fin s → Fin (D + 1)) y z = 1 / ((b : ℝ) ^ D) ^ s := by
  unfold haarKernel
  have h0 : ∀ j, detailKernel (((0 : Fin s → Fin (D + 1)) j : ℕ)) (y j) (z j) = 1 / (b : ℝ) ^ D :=
    fun j ↦ by
      rw [Pi.zero_apply, Fin.val_zero]
      exact agreeKernel_zero _ _
  rw [Finset.prod_congr rfl fun j _ ↦ h0 j, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, div_pow, one_pow]

/-- **The `s`-dimensional pair kernel in the Haar basis**:
`Π_j π_{k_j}(y_j, z_j) = b^{-sD} Σ_ℓ (Π_j w(k_j, ℓ_j)) H_ℓ(y, z)`. -/
theorem prod_pairKernel_eq_sum (hb : 1 < b) {s : ℕ} (k : Fin s → ℕ)
    (y z : Fin s → Fin D → Fin b) :
    ∏ j, pairKernel (k j) (y j) (z j) =
      (∑ ℓ : Fin s → Fin (D + 1), (∏ j, gainWeight b (k j) (ℓ j)) * haarKernel ℓ y z) /
        ((b : ℝ) ^ D) ^ s := by
  rw [Finset.prod_congr rfl fun j _ ↦ pairKernel_eq_sum hb (k j) (y j) (z j),
    Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.prod_sum (fun j (ℓ : Fin (D + 1)) ↦ gainWeight b (k j) ℓ * detailKernel ℓ (y j) (z j))]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  rw [Finset.prod_mul_distrib]
  rfl

/-- The coordinatewise nested scramble of an `s`-dimensional digit point. -/
def scrambleVec {s : ℕ} (ρ : Fin s → Scramble b D) (c : Fin s → Fin D → Fin b) :
    Fin s → Fin D → Fin b :=
  fun j ↦ scramble (ρ j) (c j)

/-- **`s`-dimensional pair law** (Owen 1997, item (iii)): with independent uniform nested
scrambles in the `s` coordinates, the fraction of scrambles sending the digit points `(c, c')`
to `(y, z)` is `Π_j π_{k_j}(y_j, z_j)`, where `k_j` is the number of common leading digits of
`c_j, c'_j`. The joint law depends on `(c, c')` only through the vector `k`. -/
theorem card_scrambleVec_pair (hb : 1 < b) {s : ℕ} (c c' y z : Fin s → Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ c = y ∧ scrambleVec ρ c' = z).card : ℝ) =
      (Fintype.card (Scramble b D) : ℝ) ^ s *
        ∏ j, pairKernel (commonPrefix (c j) (c' j)) (y j) (z j) := by
  have hset : (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
      scrambleVec ρ c = y ∧ scrambleVec ρ c' = z) = Fintype.piFinset (fun j ↦
        Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j ∧ scramble a (c' j) = z j)
      := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, scrambleVec,
      funext_iff, forall_and]
  rw [hset, Fintype.card_piFinset, Nat.cast_prod,
    Finset.prod_congr rfl (fun j _ ↦ card_scramble_pair hb _ _ _ _), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Sum over all scrambles of a function of a scrambled pair, by the pair law. -/
theorem sum_scrambleVec_pair (hb : 1 < b) {s : ℕ} (c c' : Fin s → Fin D → Fin b)
    (G : (Fin s → Fin D → Fin b) → (Fin s → Fin D → Fin b) → ℝ) :
    ∑ ρ : Fin s → Scramble b D, G (scrambleVec ρ c) (scrambleVec ρ c') =
      (Fintype.card (Scramble b D) : ℝ) ^ s * ∑ y, ∑ z,
        (∏ j, pairKernel (commonPrefix (c j) (c' j)) (y j) (z j)) * G y z := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ρ ↦ (scrambleVec ρ c, scrambleVec ρ c'))
    (fun ρ ↦ G (scrambleVec ρ c) (scrambleVec ρ c')), ← Finset.univ_product_univ,
    Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have h1 : ∀ ρ ∈ Finset.univ.filter (fun ρ : Fin s → Scramble b D ↦
      (scrambleVec ρ c, scrambleVec ρ c') = (y, z)),
      G (scrambleVec ρ c) (scrambleVec ρ c') = G y z := by
    intro ρ hρ
    obtain ⟨e1, e2⟩ := Prod.mk.inj (Finset.mem_filter.1 hρ).2
    rw [e1, e2]
  have h2 : (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
      (scrambleVec ρ c, scrambleVec ρ c') = (y, z)) = (Finset.univ.filter fun ρ ↦
        scrambleVec ρ c = y ∧ scrambleVec ρ c' = z) :=
    Finset.filter_congr fun ρ _ ↦ Prod.ext_iff
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, h2, card_scrambleVec_pair hb]
  ring

/-- **`s`-dimensional uniformity**: a fraction `b^{-sD}` of the scrambles send `c` to `y`. -/
theorem card_scrambleVec {s : ℕ} (c y : Fin s → Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Fin s → Scramble b D ↦ scrambleVec ρ c = y).card : ℝ) *
      ((b : ℝ) ^ D) ^ s = (Fintype.card (Scramble b D) : ℝ) ^ s := by
  have hset : (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦ scrambleVec ρ c = y) =
      Fintype.piFinset (fun j ↦
        Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j) := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, scrambleVec,
      funext_iff]
  rw [hset, Fintype.card_piFinset, Nat.cast_prod]
  calc (∏ j, ((Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j).card : ℝ)) *
        ((b : ℝ) ^ D) ^ s
      = ∏ j, (((Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j).card : ℝ) *
          (b : ℝ) ^ D) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ∏ _j : Fin s, (Fintype.card (Scramble b D) : ℝ) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        have := card_scramble_fiber_mul (c j) (y j)
        exact_mod_cast this
    _ = (Fintype.card (Scramble b D) : ℝ) ^ s := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Sum over all scrambles of a function of one scrambled digit point. -/
theorem sum_scrambleVec (hb : 0 < b) {s : ℕ} (c : Fin s → Fin D → Fin b)
    (G : (Fin s → Fin D → Fin b) → ℝ) :
    ∑ ρ : Fin s → Scramble b D, G (scrambleVec ρ c) =
      (Fintype.card (Scramble b D) : ℝ) ^ s * (∑ y, G y) / ((b : ℝ) ^ D) ^ s := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hpos : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  rw [← Finset.sum_fiberwise Finset.univ (fun ρ ↦ scrambleVec ρ c)
    (fun ρ ↦ G (scrambleVec ρ c)), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have h1 : ∀ ρ ∈ Finset.univ.filter (fun ρ : Fin s → Scramble b D ↦ scrambleVec ρ c = y),
      G (scrambleVec ρ c) = G y := fun ρ hρ ↦ by rw [(Finset.mem_filter.1 hρ).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← card_scrambleVec c y]
  field_simp

/-- The **variance component** `σ²_ℓ(F) = b^{-sD} Σ_{y,z} F(y) H_ℓ(y,z) F(z) ≥ 0` of a function
on the digit grid (the squared norm of its Haar component `ℓ`). -/
noncomputable def haarVar {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ) (ℓ : Fin s → Fin (D + 1)) :
    ℝ :=
  qform (haarKernel ℓ) F / ((b : ℝ) ^ D) ^ s

/-- The variance components are nonnegative. -/
theorem haarVar_nonneg (hb : 0 < b) {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ)
    (ℓ : Fin s → Fin (D + 1)) : 0 ≤ haarVar F ℓ :=
  div_nonneg (qform_haarKernel_nonneg hb ℓ F) (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)

/-- **Parseval**: the variance components add up to the mean square `b^{-sD} Σ_y F(y)²`. -/
theorem sum_haarVar (hb : 0 < b) {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ) :
    ∑ ℓ, haarVar F ℓ = (∑ y, F y ^ 2) / ((b : ℝ) ^ D) ^ s := by
  unfold haarVar qform
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single y]
  · rw [← Finset.sum_mul, ← Finset.mul_sum, sum_haarKernel hb, ite_eq_left rfl, sq]
    ring
  · intro z _ hz
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_haarKernel hb, ite_eq_right (Ne.symm hz)]
    ring
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- The component of the mean: `σ²_0 = (b^{-sD} Σ_y F(y))²`. -/
theorem haarVar_zero {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ) :
    haarVar F 0 = ((∑ y, F y) / ((b : ℝ) ^ D) ^ s) ^ 2 := by
  unfold haarVar qform
  simp only [haarKernel_zero]
  have e : ∀ y z, F y * (1 / ((b : ℝ) ^ D) ^ s) * F z = 1 / ((b : ℝ) ^ D) ^ s * (F y * F z) :=
    fun y z ↦ by ring
  simp only [e, ← Finset.mul_sum]
  rw [div_pow, sq (∑ y, F y), Finset.sum_mul]
  ring

/-- The **gain coefficients** of a point set of digit points (Owen 1997):
`Γ_ℓ = n⁻¹ Σ_{i,i'} Π_j w(k_j(i,i'), ℓ_j)`, with `k_j(i,i')` the number of common leading digits
of coordinate `j` of points `i, i'`. -/
noncomputable def gainCoeff (b : ℕ) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (ℓ : Fin s → Fin (D + 1)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∑ i', ∏ j, gainWeight b (commonPrefix (d i j) (d i' j)) (ℓ j)

/-- The gain coefficient of the mean is `n`. -/
theorem gainCoeff_zero (hb : 1 < b) {s n : ℕ} (hn : n ≠ 0) (d : Fin n → Fin s → Fin D → Fin b) :
    gainCoeff b d 0 = n := by
  unfold gainCoeff
  simp only [Pi.zero_apply, Fin.val_zero, gainWeight_zero hb, Finset.prod_const_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- Exchanging three finite sums. -/
theorem sum_sum_sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm, Finset.sum_comm]

/-- The pair sum `Σ_{y,z} Π_j π_{k_j}(y_j,z_j) F(y) F(z)` in terms of the gain weights and the
variance components. -/
theorem sum_pairKernel_mul_eq (hb : 1 < b) {s : ℕ} (k : Fin s → ℕ)
    (F : (Fin s → Fin D → Fin b) → ℝ) :
    ∑ y, ∑ z, (∏ j, pairKernel (k j) (y j) (z j)) * (F y * F z) =
      ∑ ℓ, (∏ j, gainWeight b (k j) (ℓ j)) * haarVar F ℓ := by
  unfold haarVar qform
  simp only [prod_pairKernel_eq_sum hb, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [sum_sum_sum_rotate]
  refine Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_congr rfl fun y _ ↦
    Finset.sum_congr rfl fun z _ ↦ ?_
  ring

/-- **The scrambled sum, second moment** (Owen 1997): averaging over the nested scrambles,
`E[(Σ_i F(σ d_i))²] = n Σ_ℓ Γ_ℓ σ²_ℓ(F)`. -/
theorem sum_sq_sum_scrambleVec (hb : 1 < b) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (F : (Fin s → Fin D → Fin b) → ℝ) :
    (∑ ρ : Fin s → Scramble b D, (∑ i, F (scrambleVec ρ (d i))) ^ 2) /
        (Fintype.card (Scramble b D) : ℝ) ^ s =
      n * ∑ ℓ, gainCoeff b d ℓ * haarVar F ℓ := by
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have e1 : ∀ ρ : Fin s → Scramble b D, (∑ i, F (scrambleVec ρ (d i))) ^ 2 =
      ∑ i, ∑ i', F (scrambleVec ρ (d i)) * F (scrambleVec ρ (d i')) := fun ρ ↦ by
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun ρ _ ↦ e1 ρ, ← sum_sum_sum_rotate, Finset.sum_div]
  have e2 : ∀ i i', (∑ ρ : Fin s → Scramble b D,
      F (scrambleVec ρ (d i)) * F (scrambleVec ρ (d i'))) /
        (Fintype.card (Scramble b D) : ℝ) ^ s =
      ∑ ℓ, (∏ j, gainWeight b (commonPrefix (d i j) (d i' j)) (ℓ j)) * haarVar F ℓ := by
    intro i i'
    rw [sum_scrambleVec_pair hb _ _ (fun y z ↦ F y * F z), ← sum_pairKernel_mul_eq hb]
    field_simp
  simp only [Finset.sum_div, e2]
  unfold gainCoeff
  rw [Finset.mul_sum, sum_sum_sum_rotate]
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  simp only [← Finset.sum_mul]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_mul, mul_zero]
  · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
    field_simp

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.LohGeneralProd

/-!
# The conditional variance of the product integrand concentrates

Towards Loh's (2003) CLT for `f(x) = x₀ x₁` on scrambled `(0,m,2)`-nets (post #2). Given the
scramble `ρ₀` of coordinate `0`, the error sum `S` is a sum of independent node terms of the
scramble of coordinate `1` (`LohGeneralProd`), with conditional variance
`V(ρ₀) = Σ_γ E_π[nodeTerm²]` (`condVar`). This module proves that `V` concentrates around its
mean: `E|V - E V| = o(E V)`. Each level `k₁` of the tree of coordinate `1` contributes a term
depending mainly on the level `m - k₁ - 1` of `ρ₀`; keeping only a window of `J` levels of `ρ₀`
below it (`condVarWin`, `levelVar`) changes `V` by `O(b^{-J} m/n)` in mean
(`unifAvg_abs_condVar_sub_le`), and the windowed levels `k₁, k₁'` with `|k₁ - k₁'| ≥ J` are
independent (`unifAvg_levelVar_mul`), so the windowed variance has variance `O(J m/n²)`
(`unifAvg_sq_condVarWin_sub_le`). Since `E V ≍ m/n`, choosing `J ≍ √m` gives the
concentration.

## Main results

* `dform`, `abs_dform_le`, `unifAvg_sq_dform_le`, `abs_unifAvg_sq_dform_sub_le`: the linear
  forms `Σ_c (π c - (b-1)/2) w_c` and their second moments.
* `unifAvg_sq_sum_le_of_sq`, `unifAvg_sq_sub_eq`, `unifAvg_sq_sum_sub_le_of_near`: moment
  bounds for sums of nonnegative terms that are independent at distance `≥ J`.
* `condVar`, `levelVar`, `condVarWin`; `unifAvg_abs_condVar_sub_le` (window truncation),
  `unifAvg_sq_levelVar_le`, `unifAvg_levelVar_mul` (independence of distant windows),
  `unifAvg_sq_condVarWin_sub_le` (variance of the windowed part), `unifAvg_abs_sub_avg_le`,
  `sq_unifAvg_abs_le` (assembling the concentration bound).
* `nodeBound`, `abs_nodeTerm_le`, `unifAvg_sum_sq_nodeBound_le`,
  `unifAvg_sum_pow_four_nodeBound_le`: the moments of the bounds
  `b^{-(k+1)} (b/2) Σ_c |w_{γ,c}|` on the node terms.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology

variable {b : ℕ}

/-- The linear form `Σ_c (π c - (b-1)/2) w_c` of a weight vector `w`. -/
noncomputable def dform (pm : Equiv.Perm (Fin b)) (w : Fin b → ℝ) : ℝ :=
  ∑ c, cdig pm c * w c

/-- `|Σ_c (π c - (b-1)/2) w_c| ≤ (b/2) Σ_c |w_c|`. -/
theorem abs_dform_le (pm : Equiv.Perm (Fin b)) (w : Fin b → ℝ) :
    |dform pm w| ≤ (b : ℝ) / 2 * ∑ c, |w c| := by
  unfold dform
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ ↦ ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_cdig_le pm c) (abs_nonneg _)

/-- `(Σ_c |w_c|)² ≤ b Σ_c w_c²`. -/
theorem sq_sum_abs_le (w : Fin b → ℝ) : (∑ c, |w c|) ^ 2 ≤ b * ∑ c, w c ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin b))) (f := fun c ↦ |w c|)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simpa only [sq_abs] using h

/-- `(Σ_c |w_c|)⁴ ≤ b³ Σ_c w_c⁴`. -/
theorem pow_four_sum_abs_le (w : Fin b → ℝ) : (∑ c, |w c|) ^ 4 ≤ (b : ℝ) ^ 3 * ∑ c, w c ^ 4 := by
  have h1 := sq_sum_abs_le w
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin b)))
    (f := fun c ↦ w c ^ 2)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h0 : 0 ≤ (∑ c, |w c|) ^ 2 := sq_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  calc (∑ c, |w c|) ^ 4 = ((∑ c, |w c|) ^ 2) ^ 2 := by ring
    _ ≤ ((b : ℝ) * ∑ c, w c ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (b : ℝ) ^ 2 * (∑ c, w c ^ 2) ^ 2 := by ring
    _ ≤ (b : ℝ) ^ 2 * ((b : ℝ) * ∑ c, (w c ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (b : ℝ) ^ 3 * ∑ c, w c ^ 4 := by
        rw [Finset.sum_congr rfl fun c _ ↦ (pow_mul (w c) 2 2).symm]
        ring

/-- The linear form is linear in the weights. -/
theorem dform_sub (pm : Equiv.Perm (Fin b)) (w w' : Fin b → ℝ) :
    dform pm w - dform pm w' = dform pm (fun c ↦ w c - w' c) := by
  unfold dform
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

/-- The linear form is additive in the weights. -/
theorem dform_add (pm : Equiv.Perm (Fin b)) (w w' : Fin b → ℝ) :
    dform pm w + dform pm w' = dform pm (fun c ↦ w c + w' c) := by
  unfold dform
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

/-- `E_π[(Σ_c (π c - (b-1)/2) w_c)²] ≤ (b/2)² b Σ_c w_c²`. -/
theorem unifAvg_sq_dform_le (hb : 0 < b) (w : Fin b → ℝ) :
    unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) ≤
      ((b : ℝ) / 2) ^ 2 * (b * ∑ c, w c ^ 2) := by
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
  have hb2 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  calc dform pm w ^ 2 = |dform pm w| ^ 2 := (sq_abs _).symm
    _ ≤ ((b : ℝ) / 2 * ∑ c, |w c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_dform_le pm w) 2
    _ = ((b : ℝ) / 2) ^ 2 * (∑ c, |w c|) ^ 2 := by ring
    _ ≤ ((b : ℝ) / 2) ^ 2 * (b * ∑ c, w c ^ 2) :=
        mul_le_mul_of_nonneg_left (sq_sum_abs_le w) (sq_nonneg _)

/-- **Lipschitz bound for the second moment of the linear form**:
`|E[(dform w)²] - E[(dform w')²]| ≤ (b/2)² (Σ_c |w_c - w'_c|)(Σ_c |w_c + w'_c|)`. -/
theorem abs_unifAvg_sq_dform_sub_le (w w' : Fin b → ℝ) :
    |unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) -
        unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w' ^ 2)| ≤
      ((b : ℝ) / 2) ^ 2 * ((∑ c, |w c - w' c|) * ∑ c, |w c + w' c|) := by
  rcases isEmpty_or_nonempty (Fin b) with hb | hb
  · have : b = 0 := by
      by_contra h
      exact hb.false ⟨0, Nat.pos_of_ne_zero h⟩
    subst this
    simp [unifAvg, dform]
  have hb0 : 0 < b := Fin.pos (Classical.arbitrary (Fin b))
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  have e : unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) -
      unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w' ^ 2) =
      unifAvg (fun pm ↦ dform pm (fun c ↦ w c - w' c) * dform pm (fun c ↦ w c + w' c)) := by
    rw [sub_eq_add_neg, ← neg_one_mul, ← unifAvg_const_mul, ← unifAvg_add]
    congr 1
    funext pm
    rw [← dform_sub, ← dform_add]
    ring
  rw [e]
  refine (abs_unifAvg_le _).trans ((unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _)))
  rw [abs_mul]
  have hb2 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  calc |dform pm (fun c ↦ w c - w' c)| * |dform pm (fun c ↦ w c + w' c)|
      ≤ ((b : ℝ) / 2 * ∑ c, |w c - w' c|) * ((b : ℝ) / 2 * ∑ c, |w c + w' c|) :=
        mul_le_mul (abs_dform_le _ _) (abs_dform_le _ _) (abs_nonneg _)
          (mul_nonneg hb2 (Finset.sum_nonneg fun c _ ↦ abs_nonneg _))
    _ = ((b : ℝ) / 2) ^ 2 * ((∑ c, |w c - w' c|) * ∑ c, |w c + w' c|) := by ring

/-- **Second moment of a sum from second-moment bounds of its terms**: if
`E[Y_a²] ≤ u_a²` with `u_a ≥ 0`, then `E[(Σ_a Y_a)²] ≤ (Σ_a u_a)²`. -/
theorem unifAvg_sq_sum_le_of_sq {R ι : Type*} [Fintype R] (s : Finset ι) (Y : ι → R → ℝ)
    {u : ι → ℝ} (hu : ∀ a ∈ s, 0 ≤ u a)
    (hY : ∀ a ∈ s, unifAvg (fun r ↦ Y a r ^ 2) ≤ u a ^ 2) :
    unifAvg (fun r ↦ (∑ a ∈ s, Y a r) ^ 2) ≤ (∑ a ∈ s, u a) ^ 2 := by
  have e : (fun r ↦ (∑ a ∈ s, Y a r) ^ 2) = fun r ↦ ∑ a ∈ s, ∑ a' ∈ s, Y a r * Y a' r :=
    funext fun r ↦ by rw [sq, Finset.sum_mul_sum]
  rw [e, unifAvg_sum, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a ha ↦ ?_
  rw [unifAvg_sum]
  refine Finset.sum_le_sum fun a' ha' ↦ ?_
  have h := sq_unifAvg_mul_le (Y a) (Y a')
  have hprod : (unifAvg fun r ↦ Y a r ^ 2) * (unifAvg fun r ↦ Y a' r ^ 2) ≤ (u a * u a') ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul (hY a ha) (hY a' ha') (unifAvg_nonneg fun r ↦ sq_nonneg _)
      (sq_nonneg _)
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq (h.trans hprod)
    (mul_nonneg (hu a ha) (hu a' ha')))

/-- The variance identity `E[(Z - E Z)²] = E[Z²] - (E Z)²`. -/
theorem unifAvg_sq_sub_eq {R : Type*} [Fintype R] [Nonempty R] (Z : R → ℝ) :
    unifAvg (fun r ↦ (Z r - unifAvg Z) ^ 2) = unifAvg (fun r ↦ Z r ^ 2) - unifAvg Z ^ 2 := by
  have e : (fun r ↦ (Z r - unifAvg Z) ^ 2) =
      fun r ↦ (Z r ^ 2 + (-2 * unifAvg Z) * Z r) + unifAvg Z ^ 2 :=
    funext fun r ↦ by ring
  rw [e, unifAvg_add, unifAvg_add, unifAvg_const_mul, unifAvg_const]
  ring

/-- **Variance of a sum of nonnegative terms independent at distance `≥ J`**: if
`E[X_k X_{k'}] = E X_k E X_{k'}` whenever `|k - k'| ≥ J` and `E[X_k²] ≤ A`, then
`E[(Σ_k X_k - E Σ_k X_k)²] ≤ 2 J m A`. -/
theorem unifAvg_sq_sum_sub_le_of_near {R : Type*} [Fintype R] [Nonempty R] {m J : ℕ}
    (X : Fin m → R → ℝ) (hX0 : ∀ k r, 0 ≤ X k r)
    (hind : ∀ k k' : Fin m, (k : ℕ) + J ≤ k' ∨ (k' : ℕ) + J ≤ k →
      unifAvg (fun r ↦ X k r * X k' r) = unifAvg (X k) * unifAvg (X k'))
    {A : ℝ} (hA : ∀ k, unifAvg (fun r ↦ X k r ^ 2) ≤ A) :
    unifAvg (fun r ↦ (∑ k, X k r - unifAvg (fun r' ↦ ∑ k, X k r')) ^ 2) ≤ 2 * J * m * A := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [unifAvg]
  have hA0 : 0 ≤ A := (unifAvg_nonneg fun r ↦ sq_nonneg _).trans (hA ⟨0, hm⟩)
  rw [unifAvg_sq_sub_eq]
  have e1 : unifAvg (fun r ↦ (∑ k, X k r) ^ 2) =
      ∑ k, ∑ k', unifAvg (fun r ↦ X k r * X k' r) := by
    rw [show (fun r ↦ (∑ k, X k r) ^ 2) = fun r ↦ ∑ k, ∑ k', X k r * X k' r from
      funext fun r ↦ by rw [sq, Finset.sum_mul_sum], unifAvg_sum]
    exact Finset.sum_congr rfl fun k _ ↦ unifAvg_sum _ _
  have e2 : unifAvg (fun r' ↦ ∑ k, X k r') ^ 2 =
      ∑ k, ∑ k', unifAvg (X k) * unifAvg (X k') := by
    rw [unifAvg_sum, sq, Finset.sum_mul_sum]
  rw [e1, e2]
  simp only [← Finset.sum_sub_distrib]
  have hterm : ∀ k k' : Fin m, unifAvg (fun r ↦ X k r * X k' r) -
      unifAvg (X k) * unifAvg (X k') ≤
      if (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J then A else 0 := by
    intro k k'
    split_ifs with h
    · have h1 : unifAvg (fun r ↦ X k r * X k' r) ≤ A := by
        have h3 : unifAvg (fun r ↦ X k r * X k' r) ≤
            unifAvg (fun r ↦ 1 / 2 * (X k r ^ 2 + X k' r ^ 2)) :=
          unifAvg_mono fun r ↦ by nlinarith [sq_nonneg (X k r - X k' r)]
        rw [unifAvg_const_mul, unifAvg_add] at h3
        linarith [hA k, hA k']
      have h2 : 0 ≤ unifAvg (X k) * unifAvg (X k') :=
        mul_nonneg (unifAvg_nonneg (hX0 k)) (unifAvg_nonneg (hX0 k'))
      linarith
    · rw [hind k k' (by omega), sub_self]
  have hcard : ∀ k : Fin m, (Finset.univ.filter fun k' : Fin m ↦
      (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J).card ≤ 2 * J := by
    intro k
    refine (Finset.card_le_card_of_injOn (fun k' : Fin m ↦ (k' : ℕ))
      (t := Finset.Ico ((k : ℕ) + 1 - J) ((k : ℕ) + J)) (fun k' hk' ↦ ?_)
      (fun x _ y _ hxy ↦ Fin.ext hxy)).trans ?_
    · rw [Finset.mem_coe, Finset.mem_filter] at hk'
      rw [Finset.mem_coe, Finset.mem_Ico]
      dsimp only
      omega
    · rw [Nat.card_Ico]
      omega
  calc ∑ k, ∑ k', (unifAvg (fun r ↦ X k r * X k' r) - unifAvg (X k) * unifAvg (X k'))
      ≤ ∑ k : Fin m, ∑ k' : Fin m,
          (if (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J then A else 0) :=
        Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun k' _ ↦ hterm k k'
    _ = ∑ k : Fin m, A * (Finset.univ.filter fun k' : Fin m ↦
          (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J).card := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
    _ ≤ ∑ _k : Fin m, A * (2 * J : ℕ) := by
        refine Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left ?_ hA0
        exact_mod_cast hcard k
    _ = 2 * J * m * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- `x y ≤ (λ x² + y²/λ)/2` for `λ > 0`. -/
theorem mul_le_half_add_sq {x y l : ℝ} (hl : 0 < l) : x * y ≤ (l * x ^ 2 + y ^ 2 / l) / 2 := by
  have h : l * (2 * (x * y)) ≤ l * (l * x ^ 2 + y ^ 2 / l) := by
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hl.ne']
    nlinarith [sq_nonneg (l * x - y)]
  have := le_of_mul_le_mul_left h hl
  linarith

/-- `Σ x_a² ≤ (Σ x_a)²` for nonnegative `x`. -/
theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ a ∈ s, 0 ≤ x a) :
    ∑ a ∈ s, x a ^ 2 ≤ (∑ a ∈ s, x a) ^ 2 := by
  rw [sq (∑ a ∈ s, x a), Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha ↦ ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hx ha) (hx a ha)

/-- `b^{-(k+1)} b^{-(m-k)} = b^{-(m+1)}` for `k < m`. -/
theorem digWt_mul_digWt {m : ℕ} (k : Fin m) : digWt b k * digWt b (m - k - 1) = digWt b m := by
  unfold digWt
  rw [← mul_inv, ← pow_add]
  congr 2
  have := k.isLt
  omega

/-- `b^{-(l+J+1)} = b^{-(l+1)} b^{-J}`. -/
theorem digWt_add (b l J : ℕ) : digWt b (l + J) = digWt b l * ((b : ℝ) ^ J)⁻¹ := by
  unfold digWt
  rw [← mul_inv, ← pow_add]
  congr 2
  omega

/-- **The points of a level are partitioned by the nodes and their children**:
`Σ_t Σ_c #(cellSet (k, t) c) = n`. -/
theorem sum_card_cellSet {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (k : Fin m) :
    ∑ t : Fin m → Option (Fin b), ∑ c, ((cellSet d (k, t) c).card : ℝ) = n := by
  classical
  have h1 : ∀ t : Fin m → Option (Fin b),
      ∑ c, ((cellSet d (k, t) c).card : ℝ) = (nodeSet d (k, t)).card := by
    intro t
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i ↦ d i 1 k) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _), Nat.cast_sum]
    rfl
  rw [Finset.sum_congr rfl fun t _ ↦ h1 t]
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (f := fun i ↦ truncDigits k (d i 1)) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (∑ t : Fin m → Option (Fin b), (nodeSet d (k, t)).card) = n := h2.symm
  rw [← Nat.cast_sum, h3]

/-- The total over all nodes: `Σ_γ Σ_c #(cellSet γ c) = m n`. -/
theorem sum_card_cellSet_all {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) :
    ∑ γ : Fin m × (Fin m → Option (Fin b)), ∑ c, ((cellSet d γ c).card : ℝ) = m * n := by
  rw [Fintype.sum_prod_type]
  simp only [sum_card_cellSet d, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Splitting the top window of levels at `lo + J`. -/
theorem wwin_split_top {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) (lo J : ℕ) :
    wwin d ρ₀ γ c lo m = wwin d ρ₀ γ c lo (lo + J) + wwin d ρ₀ γ c (lo + J) m := by
  unfold wwin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not (levelWin m lo m)
    (fun k : Fin m ↦ (k : ℕ) < lo + J)]
  congr 1
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    have := k.isLt
    omega
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    have := k.isLt
    omega

/-- A window part of a node weight depends only on the levels in the window. -/
theorem wwin_congr {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) {ρ ρ' : Scramble b m}
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) {lo hi : ℕ}
    (h : ∀ k ∈ levelWin m lo hi, ∀ x, ρ (k, x) = ρ' (k, x)) :
    wwin d ρ γ c lo hi = wwin d ρ' γ c lo hi := by
  unfold wwin
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k hk ↦ by rw [h k hk]

/-- `E_π[(a · dform π w)²] = a² E_π[(dform π w)²]`. -/
theorem unifAvg_sq_mul_dform (a : ℝ) (w : Fin b → ℝ) :
    unifAvg (fun pm : Equiv.Perm (Fin b) ↦ (a * dform pm w) ^ 2) =
      a ^ 2 * unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) := by
  rw [← unifAvg_const_mul]
  congr 1
  funext pm
  ring

/-- The conditional variance `V(ρ₀) = Σ_γ E_π[nodeTerm²]` of `S` given `ρ₀`. -/
noncomputable def condVar {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m) :
    ℝ :=
  ∑ γ, unifAvg (fun pm ↦ nodeTerm d ρ₀ γ pm ^ 2)

/-- The level-`k` part of the windowed conditional variance: only the levels
`m - k - 1 ≤ k₀ < m - k - 1 + J` of `ρ₀` are kept in the node weights. -/
noncomputable def levelVar {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (J : ℕ) (k : Fin m) : ℝ :=
  ∑ t : Fin m → Option (Fin b), unifAvg (fun pm : Equiv.Perm (Fin b) ↦
    (digWt b k * dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)

/-- The windowed conditional variance `Σ_k levelVar`. -/
noncomputable def condVarWin {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (J : ℕ) : ℝ :=
  ∑ k : Fin m, levelVar d ρ₀ J k

/-- **One node: the window truncation error of the conditional variance**:
`E|E_π[nodeTerm²] - E_π[windowed²]| ≤ 5 b (b/2)⁴ b^{-J} b^{-2(m+1)} #(points below γ)`. -/
theorem unifAvg_abs_nodeVar_sub_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (k : Fin m) (t : Fin m → Option (Fin b)) (J : ℕ) :
    unifAvg (fun ρ₀ : Scramble b m ↦ |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
      unifAvg (fun pm : Equiv.Perm (Fin b) ↦
        (digWt b k * dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)|) ≤
      5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 *
        ∑ c, ((cellSet d (k, t) c).card : ℝ) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  set lo := m - (k : ℕ) - 1 with hlo
  set h := (b : ℝ) / 2 with hh
  set l : ℝ := (b : ℝ) ^ J with hl
  have hl0 : 0 < l := pow_pos hbR J
  set wk := digWt b k with hwk
  set W := digWt b lo with hW
  have hhlo : m ≤ lo + (k, t).1 + 1 := by
    change m ≤ lo + (k : ℕ) + 1
    have := k.isLt
    omega
  have hhloJ : m ≤ lo + J + (k, t).1 + 1 := by
    change m ≤ lo + J + (k : ℕ) + 1
    have := k.isLt
    omega
  set α := wk ^ 2 * h ^ 2 * (l * b) / 2 with hα
  set β := wk ^ 2 * h ^ 2 * (l⁻¹ * b) with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  -- the pointwise bound
  have hpt : ∀ ρ₀ : Scramble b m, |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
      unifAvg (fun pm : Equiv.Perm (Fin b) ↦
        (digWt b k * dform pm (fun c ↦ wwin d ρ₀ (k, t) c lo (lo + J))) ^ 2)| ≤
      ∑ c, (α * wwin d ρ₀ (k, t) c (lo + J) m ^ 2 + β * wwin d ρ₀ (k, t) c lo m ^ 2 +
        β * wwin d ρ₀ (k, t) c lo (lo + J) ^ 2) := by
    intro ρ₀
    set w : Fin b → ℝ := fun c ↦ wwin d ρ₀ (k, t) c lo m with hw
    set wJ : Fin b → ℝ := fun c ↦ wwin d ρ₀ (k, t) c lo (lo + J) with hwJ
    set D : Fin b → ℝ := fun c ↦ wwin d ρ₀ (k, t) c (lo + J) m with hD
    have hwD : ∀ c, w c - wJ c = D c := fun c ↦ by
      rw [hw, hwJ, hD]
      simp only
      rw [wwin_split_top d ρ₀ (k, t) c lo J]
      ring
    have hnt : ∀ pm, nodeTerm d ρ₀ (k, t) pm = wk * dform pm w := fun pm ↦ by
      change digWt b k * ∑ c, cdig pm c * nodeW d ρ₀ (k, t) c = wk * ∑ c, cdig pm c * w c
      congr 1
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [hw, nodeW_eq_wwin hb0 hnet]
    rw [show (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) = fun pm ↦ (wk * dform pm w) ^ 2 from
      funext fun pm ↦ by rw [hnt], unifAvg_sq_mul_dform, unifAvg_sq_mul_dform, ← mul_sub,
      abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_unifAvg_sq_dform_sub_le w wJ
    have h2 : (∑ c, |w c - wJ c|) * (∑ c, |w c + wJ c|) ≤
        (l * (b * ∑ c, D c ^ 2) + (b * ∑ c, (2 * w c ^ 2 + 2 * wJ c ^ 2)) / l) / 2 := by
      refine (mul_le_half_add_sq hl0).trans ?_
      have hA : (∑ c, |w c - wJ c|) ^ 2 ≤ b * ∑ c, D c ^ 2 := by
        rw [Finset.sum_congr rfl fun c _ ↦ by rw [hwD c]]
        exact sq_sum_abs_le D
      have hB : (∑ c, |w c + wJ c|) ^ 2 ≤ b * ∑ c, (2 * w c ^ 2 + 2 * wJ c ^ 2) := by
        refine (sq_sum_abs_le _).trans ?_
        gcongr with c
        nlinarith [sq_nonneg (w c - wJ c)]
      have := mul_le_mul_of_nonneg_left hA hl0.le
      have := div_le_div_of_nonneg_right hB hl0.le
      linarith
    calc wk ^ 2 * |unifAvg (fun pm ↦ dform pm w ^ 2) - unifAvg (fun pm ↦ dform pm wJ ^ 2)|
        ≤ wk ^ 2 * (h ^ 2 * ((∑ c, |w c - wJ c|) * ∑ c, |w c + wJ c|)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ wk ^ 2 * (h ^ 2 * ((l * (b * ∑ c, D c ^ 2) +
            (b * ∑ c, (2 * w c ^ 2 + 2 * wJ c ^ 2)) / l) / 2)) := by
          gcongr
      _ = ∑ c, (α * D c ^ 2 + β * w c ^ 2 + β * wJ c ^ 2) := by
          rw [hα, hβ, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
          field_simp
          ring
  refine (unifAvg_mono hpt).trans ?_
  rw [unifAvg_sum]
  simp only [unifAvg_add, unifAvg_const_mul]
  -- the moments
  have hD2 : ∀ c, unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c (lo + J) m ^ 2) ≤
      (cellSet d (k, t) c).card * (h ^ 2 * (2 * (W * l⁻¹) ^ 2)) := fun c ↦ by
    have := unifAvg_sq_wwin_le hb hnet (k, t) c (lo := lo + J) (hi := m) hhloJ
    rwa [digWt_add] at this
  have hw2 : ∀ c, unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo m ^ 2) ≤
      (cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2)) := fun c ↦
    unifAvg_sq_wwin_le hb hnet (k, t) c (lo := lo) (hi := m) hhlo
  have hwJ2 : ∀ c, unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo (lo + J) ^ 2) ≤
      (cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2)) := fun c ↦
    unifAvg_sq_wwin_le hb hnet (k, t) c (lo := lo) (hi := lo + J) hhlo
  have hWm : wk * W = digWt b m := digWt_mul_digWt k
  calc ∑ c, (α * unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c (lo + J) m ^ 2) +
        β * unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo m ^ 2) +
        β * unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo (lo + J) ^ 2))
      ≤ ∑ c, (α * ((cellSet d (k, t) c).card * (h ^ 2 * (2 * (W * l⁻¹) ^ 2))) +
          β * ((cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2))) +
          β * ((cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2)))) := by
        gcongr with c
        · exact hD2 c
        · exact hw2 c
        · exact hwJ2 c
    _ = 5 * b * h ^ 4 * l⁻¹ * (wk * W) ^ 2 * ∑ c, ((cellSet d (k, t) c).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [hα, hβ]
        field_simp
        ring
    _ = _ := by rw [hWm]

/-- **The window truncation error of the conditional variance**:
`E|V - V_J| ≤ 5 b (b/2)⁴ b^{-J} b^{-2(m+1)} m n`. -/
theorem unifAvg_abs_condVar_sub_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (J : ℕ) :
    unifAvg (fun ρ₀ : Scramble b m ↦ |condVar d ρ₀ - condVarWin d ρ₀ J|) ≤
      5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 * (m * (b ^ m : ℕ)) := by
  have hpt : ∀ ρ₀ : Scramble b m, |condVar d ρ₀ - condVarWin d ρ₀ J| ≤
      ∑ k : Fin m, ∑ t : Fin m → Option (Fin b),
        |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
          unifAvg (fun pm : Equiv.Perm (Fin b) ↦ (digWt b k *
            dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)| := by
    intro ρ₀
    unfold condVar condVarWin levelVar
    rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine (unifAvg_mono hpt).trans ?_
  rw [unifAvg_sum]
  simp only [unifAvg_sum]
  calc ∑ k : Fin m, ∑ t : Fin m → Option (Fin b), unifAvg (fun ρ₀ : Scramble b m ↦
        |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
          unifAvg (fun pm : Equiv.Perm (Fin b) ↦ (digWt b k *
            dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)|)
      ≤ ∑ k : Fin m, ∑ t : Fin m → Option (Fin b),
          5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 *
            ∑ c, ((cellSet d (k, t) c).card : ℝ) :=
        Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun t _ ↦
          unifAvg_abs_nodeVar_sub_le hb hnet k t J
    _ = 5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 * (m * (b ^ m : ℕ)) := by
        rw [← sum_card_cellSet_all d, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.mul_sum]

/-- The level parts of the windowed conditional variance are nonnegative. -/
theorem levelVar_nonneg {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (J : ℕ) (k : Fin m) : 0 ≤ levelVar d ρ₀ J k :=
  Finset.sum_nonneg fun _ _ ↦ unifAvg_nonneg fun _ ↦ sq_nonneg _

/-- **The second moment of a level part**: `E[levelVar²] ≤ (4 b (b/2)⁴ b^{-2(m+1)} n)²`. -/
theorem unifAvg_sq_levelVar_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (J : ℕ) (k : Fin m) :
    unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k ^ 2) ≤
      (4 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * (b ^ m : ℕ)) ^ 2 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  set lo := m - (k : ℕ) - 1 with hlo
  set h := (b : ℝ) / 2 with hh
  set wk := digWt b k with hwk
  set W := digWt b lo with hW
  set Y : (Fin m → Option (Fin b)) × Fin b → Scramble b m → ℝ :=
    fun a ρ₀ ↦ wwin d ρ₀ (k, a.1) a.2 lo (lo + J) ^ 2 with hY
  have hhlo : ∀ t : Fin m → Option (Fin b), m ≤ lo + (k, t).1 + 1 := fun t ↦ by
    change m ≤ lo + (k : ℕ) + 1
    have := k.isLt
    omega
  have hle : ∀ ρ₀, levelVar d ρ₀ J k ≤ wk ^ 2 * (h ^ 2 * b) * ∑ a, Y a ρ₀ := by
    intro ρ₀
    unfold levelVar
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    rw [unifAvg_sq_mul_dform]
    refine (mul_le_mul_of_nonneg_left (unifAvg_sq_dform_le hb0 _) (sq_nonneg _)).trans
      (le_of_eq ?_)
    rw [hY, hwk, hh]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    ring
  have hpt : ∀ ρ₀, levelVar d ρ₀ J k ^ 2 ≤ (wk ^ 2 * (h ^ 2 * b)) ^ 2 * (∑ a, Y a ρ₀) ^ 2 := by
    intro ρ₀
    rw [← mul_pow]
    exact pow_le_pow_left₀ (levelVar_nonneg d ρ₀ J k) (hle ρ₀) 2
  refine (unifAvg_mono hpt).trans ?_
  rw [unifAvg_const_mul]
  set u : (Fin m → Option (Fin b)) × Fin b → ℝ :=
    fun a ↦ 2 * ((cellSet d (k, a.1) a.2).card * (h ^ 2 * (2 * W ^ 2))) with hu
  have hu0 : ∀ a ∈ (Finset.univ : Finset ((Fin m → Option (Fin b)) × Fin b)), 0 ≤ u a :=
    fun a _ ↦ by rw [hu]; positivity
  have hY2 : ∀ a ∈ (Finset.univ : Finset ((Fin m → Option (Fin b)) × Fin b)),
      unifAvg (fun ρ₀ ↦ Y a ρ₀ ^ 2) ≤ u a ^ 2 := by
    intro a _
    have h4 := unifAvg_pow_four_wwin_le hb hnet (k, a.1) a.2 (lo := lo) (hi := lo + J)
      (hhlo a.1)
    rw [hY]
    refine le_trans (le_of_eq ?_) (h4.trans ?_)
    · congr 1
      funext ρ₀
      ring
    · have e : u a = 2 * (((cellSet d (k, a.1) a.2).card : ℝ) *
          (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2))) := rfl
      rw [e]
      have : 0 ≤ (((cellSet d (k, a.1) a.2).card : ℝ) *
          (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2))) ^ 2 := sq_nonneg _
      nlinarith
  have hsum := unifAvg_sq_sum_le_of_sq Finset.univ Y hu0 hY2
  have hus : ∑ a, u a = 4 * h ^ 2 * W ^ 2 * (b ^ m : ℕ) := by
    rw [hu, Fintype.sum_prod_type]
    simp only
    rw [← sum_card_cellSet d k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hus] at hsum
  have hWm : wk * W = digWt b m := digWt_mul_digWt k
  calc (wk ^ 2 * (h ^ 2 * b)) ^ 2 * unifAvg (fun ρ₀ ↦ (∑ a, Y a ρ₀) ^ 2)
      ≤ (wk ^ 2 * (h ^ 2 * b)) ^ 2 * (4 * h ^ 2 * W ^ 2 * (b ^ m : ℕ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (4 * b * h ^ 4 * (wk * W) ^ 2 * (b ^ m : ℕ)) ^ 2 := by ring
    _ = _ := by rw [hWm]

/-- **Distant level parts are independent**: if `k + J ≤ k'` or `k' + J ≤ k`, the windows of
levels of `ρ₀` used by `levelVar k` and `levelVar k'` are disjoint. -/
theorem unifAvg_levelVar_mul {m : ℕ} (d : Fin (b ^ m) → Fin 2 → Fin m → Fin b) (J : ℕ)
    (k k' : Fin m) (hkk : (k : ℕ) + J ≤ k' ∨ (k' : ℕ) + J ≤ k) :
    unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k * levelVar d ρ₀ J k') =
      unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k) *
        unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k') := by
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  have hk := k.isLt
  have hk' := k'.isLt
  refine unifAvg_mul_of_disjoint (fun γ₀ : Fin m × (Fin m → Option (Fin b)) ↦
    m - (k : ℕ) - 1 ≤ γ₀.1 ∧ (γ₀.1 : ℕ) < m - (k : ℕ) - 1 + J) (fun ρ ρ' hρ ↦ ?_)
    (fun ρ ρ' hρ ↦ ?_)
  · unfold levelVar
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [show (fun c ↦ wwin d ρ (k, t) c (m - k - 1) (m - k - 1 + J)) =
      fun c ↦ wwin d ρ' (k, t) c (m - k - 1) (m - k - 1 + J) from funext fun c ↦
        wwin_congr d (k, t) c fun k₀ hk₀ x ↦ hρ (k₀, x) (Finset.mem_filter.1 hk₀).2]
  · unfold levelVar
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [show (fun c ↦ wwin d ρ (k', t) c (m - k' - 1) (m - k' - 1 + J)) =
      fun c ↦ wwin d ρ' (k', t) c (m - k' - 1) (m - k' - 1 + J) from funext fun c ↦
        wwin_congr d (k', t) c fun k₀ hk₀ x ↦ hρ (k₀, x) (by
          have := (Finset.mem_filter.1 hk₀).2
          simp only
          omega)]

/-- **The variance of the windowed conditional variance**:
`E[(V_J - E V_J)²] ≤ 2 J m (4 b (b/2)⁴ b^{-2(m+1)} n)²`. -/
theorem unifAvg_sq_condVarWin_sub_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (J : ℕ) :
    unifAvg (fun ρ₀ : Scramble b m ↦ (condVarWin d ρ₀ J -
      unifAvg (fun ρ₀' : Scramble b m ↦ condVarWin d ρ₀' J)) ^ 2) ≤
      2 * J * m * (4 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * (b ^ m : ℕ)) ^ 2 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  exact unifAvg_sq_sum_sub_le_of_near (fun k ρ₀ ↦ levelVar d ρ₀ J k)
    (fun k ρ₀ ↦ levelVar_nonneg d ρ₀ J k) (fun k k' hkk ↦ unifAvg_levelVar_mul d J k k' hkk)
    (fun k ↦ unifAvg_sq_levelVar_le hb hnet J k)

/-- `E|V - E V| ≤ 2 E|V - W| + E|W - E W|`. -/
theorem unifAvg_abs_sub_avg_le {R : Type*} [Fintype R] [Nonempty R] (V W : R → ℝ) :
    unifAvg (fun r ↦ |V r - unifAvg V|) ≤
      2 * unifAvg (fun r ↦ |V r - W r|) + unifAvg (fun r ↦ |W r - unifAvg W|) := by
  have hEW : |unifAvg W - unifAvg V| ≤ unifAvg (fun r ↦ |V r - W r|) := by
    have e : unifAvg W - unifAvg V = unifAvg (fun r ↦ W r - V r) := by
      rw [sub_eq_add_neg, ← neg_one_mul, ← unifAvg_const_mul, ← unifAvg_add]
      congr 1
      funext r
      ring
    rw [e]
    refine (abs_unifAvg_le _).trans (le_of_eq ?_)
    congr 1
    funext r
    rw [abs_sub_comm]
  have hpt : ∀ r, |V r - unifAvg V| ≤ |V r - W r| + |W r - unifAvg W| +
      |unifAvg W - unifAvg V| := fun r ↦ by
    calc |V r - unifAvg V| = |(V r - W r) + (W r - unifAvg W) + (unifAvg W - unifAvg V)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans
          (le_of_eq (by ring))
  have h := unifAvg_mono hpt
  rw [unifAvg_add, unifAvg_add, unifAvg_const] at h
  linarith

/-- `(E|Z|)² ≤ E[Z²]`. -/
theorem sq_unifAvg_abs_le {R : Type*} [Fintype R] (Z : R → ℝ) :
    (unifAvg fun r ↦ |Z r|) ^ 2 ≤ unifAvg fun r ↦ Z r ^ 2 := by
  refine (sq_unifAvg_le _).trans (le_of_eq ?_)
  congr 1
  funext r
  rw [sq_abs]

/-- The bound `b^{-(k+1)} (b/2) Σ_c |w_{γ,c}|` on the node term of `γ = (k, t)`. -/
noncomputable def nodeBound {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) : ℝ :=
  digWt b γ.1 * ((b : ℝ) / 2) * ∑ c, |nodeW d ρ₀ γ c|

/-- The node terms are bounded by `nodeBound`. -/
theorem abs_nodeTerm_le (hb : 0 < b) {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ₀ : Scramble b m) (γ : Fin m × (Fin m → Option (Fin b))) (pm : Equiv.Perm (Fin b)) :
    |nodeTerm d ρ₀ γ pm| ≤ nodeBound d ρ₀ γ := by
  change |digWt b γ.1 * dform pm (nodeW d ρ₀ γ)| ≤ _
  rw [abs_mul, abs_of_pos (digWt_pos hb _), nodeBound, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_dform_le pm _) (digWt_pos hb _).le

/-- **Second moments of the node bounds**: `E Σ_γ nodeBound² ≤ 2 b (b/2)⁴ b^{-2(m+1)} m n`. -/
theorem unifAvg_sum_sq_nodeBound_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    unifAvg (fun ρ₀ : Scramble b m ↦ ∑ γ, nodeBound d ρ₀ γ ^ 2) ≤
      2 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * (m * (b ^ m : ℕ)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  rw [unifAvg_sum]
  have hγ : ∀ γ : Fin m × (Fin m → Option (Fin b)),
      unifAvg (fun ρ₀ : Scramble b m ↦ nodeBound d ρ₀ γ ^ 2) ≤
        2 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * ∑ c, ((cellSet d γ c).card : ℝ) := by
    intro γ
    have hhlo : m ≤ (m - (γ.1 : ℕ) - 1) + γ.1 + 1 := by
      have := γ.1.isLt
      omega
    have hpt : ∀ ρ₀ : Scramble b m, nodeBound d ρ₀ γ ^ 2 ≤
        ∑ c, (digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * b) *
          wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 2 := by
      intro ρ₀
      unfold nodeBound
      rw [mul_pow, mul_pow]
      have := sq_sum_abs_le (fun c ↦ nodeW d ρ₀ γ c)
      simp only [nodeW_eq_wwin hb0 hnet] at this ⊢
      calc digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * (∑ c, |wwin d ρ₀ γ c (m - γ.1 - 1) m|) ^ 2
          ≤ digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 *
            (b * ∑ c, wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ ↦ by ring
    refine (unifAvg_mono hpt).trans ?_
    rw [unifAvg_sum]
    simp only [unifAvg_const_mul]
    calc ∑ c, digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * b *
          unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 2)
        ≤ ∑ c, digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * b *
          ((cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b (m - γ.1 - 1) ^ 2))) := by
          gcongr with c
          exact unifAvg_sq_wwin_le hb hnet γ c hhlo
      _ = 2 * b * ((b : ℝ) / 2) ^ 4 * (digWt b γ.1 * digWt b (m - γ.1 - 1)) ^ 2 *
            ∑ c, ((cellSet d γ c).card : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ ↦ by ring
      _ = _ := by rw [digWt_mul_digWt]
  refine (Finset.sum_le_sum fun γ _ ↦ hγ γ).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, sum_card_cellSet_all]

/-- **Fourth moments of the node bounds**: `E Σ_γ nodeBound⁴ ≤ 12 b³ (b/2)⁸ b^{-4(m+1)} m n²`. -/
theorem unifAvg_sum_pow_four_nodeBound_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    unifAvg (fun ρ₀ : Scramble b m ↦ ∑ γ, nodeBound d ρ₀ γ ^ 4) ≤
      12 * (b : ℝ) ^ 3 * ((b : ℝ) / 2) ^ 8 * digWt b m ^ 4 * (m * ((b ^ m : ℕ) : ℝ) ^ 2) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  rw [unifAvg_sum]
  have hγ : ∀ γ : Fin m × (Fin m → Option (Fin b)),
      unifAvg (fun ρ₀ : Scramble b m ↦ nodeBound d ρ₀ γ ^ 4) ≤
        12 * (b : ℝ) ^ 3 * ((b : ℝ) / 2) ^ 8 * digWt b m ^ 4 *
          ∑ c, ((cellSet d γ c).card : ℝ) ^ 2 := by
    intro γ
    have hhlo : m ≤ (m - (γ.1 : ℕ) - 1) + γ.1 + 1 := by
      have := γ.1.isLt
      omega
    have hpt : ∀ ρ₀ : Scramble b m, nodeBound d ρ₀ γ ^ 4 ≤
        ∑ c, (digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (b : ℝ) ^ 3) *
          wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 4 := by
      intro ρ₀
      unfold nodeBound
      rw [mul_pow, mul_pow]
      have := pow_four_sum_abs_le (fun c ↦ nodeW d ρ₀ γ c)
      simp only [nodeW_eq_wwin hb0 hnet] at this ⊢
      calc digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (∑ c, |wwin d ρ₀ γ c (m - γ.1 - 1) m|) ^ 4
          ≤ digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 *
            ((b : ℝ) ^ 3 * ∑ c, wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 4) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ ↦ by ring
    refine (unifAvg_mono hpt).trans ?_
    rw [unifAvg_sum]
    simp only [unifAvg_const_mul]
    calc ∑ c, digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (b : ℝ) ^ 3 *
          unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 4)
        ≤ ∑ c, digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (b : ℝ) ^ 3 *
          (3 * ((cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 *
            (2 * digWt b (m - γ.1 - 1) ^ 2))) ^ 2) := by
          gcongr with c
          exact unifAvg_pow_four_wwin_le hb hnet γ c hhlo
      _ = 12 * (b : ℝ) ^ 3 * ((b : ℝ) / 2) ^ 8 * (digWt b γ.1 * digWt b (m - γ.1 - 1)) ^ 4 *
            ∑ c, ((cellSet d γ c).card : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ ↦ by ring
      _ = _ := by rw [digWt_mul_digWt]
  refine (Finset.sum_le_sum fun γ _ ↦ hγ γ).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Fintype.sum_prod_type]
  calc ∑ k : Fin m, ∑ t : Fin m → Option (Fin b), ∑ c, ((cellSet d (k, t) c).card : ℝ) ^ 2
      ≤ ∑ _k : Fin m, ((b ^ m : ℕ) : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [← sum_card_cellSet d k, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
        exact sum_sq_le_sq_sum _ fun a _ ↦ Nat.cast_nonneg _
    _ = m * ((b ^ m : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end RQMCMarkov.OwenScrambling

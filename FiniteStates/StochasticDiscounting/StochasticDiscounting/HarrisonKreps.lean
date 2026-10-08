/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.Basics

/-!
# Incomplete markets: the Harrison–Kreps pricing operator

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.3.3 (pp. 209–211).

With heterogeneous beliefs `Pᵢ` and risk-neutral agents discounting at
`β ∈ (0, 1)`, the equilibrium price of an ex-dividend claim on `d ≥ 0` solves the
nonlinear equation (6.42), `π(x) = maxᵢ β ∑ (π(x') + d(x'))Pᵢ(x, x')`. The
operator `T` of (6.43) maps `ℝ^X₊` into itself and is a contraction of modulus
`β` under the supremum norm, by Lemma 2.2.2, so (6.42) has a unique solution in
`ℝ^X₊`, computable by successive approximation. Exercise 6.3.9 gives the
alternative proof through Blackwell's condition. The index set of beliefs is any
nonempty finite type, the book's `{1, 2}` included.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The Harrison–Kreps operator (6.43): `(Tπ)(x) = maxᵢ β ∑ (π(x') + d(x'))Pᵢ(x, x')`. -/
noncomputable def hkOp (β : ℝ) (P : ι → Matrix X X ℝ) (d π : X → ℝ) : X → ℝ := fun x =>
  univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x'

theorem hkOp_apply (β : ℝ) (P : ι → Matrix X X ℝ) (d π : X → ℝ) (x : X) :
    hkOp β P d π x = univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x' := rfl

/-- `π` solves (6.42) iff it is a fixed point of `T` (p. 210). -/
theorem isFixedPt_hkOp_iff (β : ℝ) (P : ι → Matrix X X ℝ) (d π : X → ℝ) :
    IsFixedPt (hkOp β P d) π ↔
      ∀ x, π x = univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x' :=
  ⟨fun h x => (congrFun h.eq x).symm, fun h => funext fun x => (h x).symm⟩

/-- The nonnegative orthant `ℝ^X₊`. -/
def nonnegFns (X : Type*) : Set (X → ℝ) := {π | ∀ x, 0 ≤ π x}

omit [Fintype X] in
theorem isClosed_nonnegFns : IsClosed (nonnegFns X) := by
  have : nonnegFns X = ⋂ x, {π : X → ℝ | 0 ≤ π x} := by
    ext π
    simp [nonnegFns]
  rw [this]
  exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)

/-- `T` maps `ℝ^X₊` into itself when `β ≥ 0`, `d ≥ 0` and the `Pᵢ` are Markov (p. 210). -/
theorem hkOp_mapsTo {β : ℝ} (hβ : 0 ≤ β) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i))
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) : Set.MapsTo (hkOp β P d) (nonnegFns X) (nonnegFns X) := by
  intro π hπ x
  rw [hkOp_apply]
  have h0 : 0 ≤ β * ∑ x', (π x' + d x') * P (Classical.arbitrary ι) x x' :=
    mul_nonneg hβ (sum_nonneg fun x' _ =>
      mul_nonneg (add_nonneg (hπ x') (hd x')) ((hP (Classical.arbitrary ι)).nonneg x x'))
  exact h0.trans (Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x') (mem_univ _))

/-- The estimate of p. 210: `|(Tp)(x) − (Tq)(x)| ≤ β‖p − q‖_∞`, by Lemma 2.2.2 and the Markov
property of each `Pᵢ`. -/
theorem abs_hkOp_sub_le {β : ℝ} (hβ : 0 ≤ β) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i))
    (d p q : X → ℝ) (x : X) : |hkOp β P d p x - hkOp β P d q x| ≤ β * ‖p - q‖ := by
  rw [hkOp_apply, hkOp_apply]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg hβ, ← sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  have h := (hP i).abs_mulVec_sub_le p q x
  simp only [mulVec, dotProduct] at h
  rw [← sum_sub_distrib] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- `T` is a contraction of modulus `β` on `ℝ^X₊` under the supremum norm (p. 211). -/
theorem isContractionOn_hkOp {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ι → Matrix X X ℝ}
    (hP : ∀ i, IsMarkov (P i)) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) :
    IsContractionOn (hkOp β P d) (nonnegFns X) β where
  mapsTo := hkOp_mapsTo hβ0 hP hd
  nonneg := hβ0
  lt_one := hβ1
  norm_sub_le p _ q _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_hkOp_sub_le hβ0 hP d p q x

/-- The Harrison–Kreps equilibrium (p. 211): (6.42) has a unique solution `π*` in `ℝ^X₊`, and
successive approximation from any `π ∈ ℝ^X₊` converges to it. -/
theorem existsUnique_hk_price {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ι → Matrix X X ℝ}
    (hP : ∀ i, IsMarkov (P i)) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) :
    ∃ π' ∈ nonnegFns X, IsFixedPt (hkOp β P d) π' ∧
      (∀ π ∈ nonnegFns X, IsFixedPt (hkOp β P d) π → π = π') ∧
      ∀ π ∈ nonnegFns X, Tendsto (fun k : ℕ => (hkOp β P d)^[k] π) atTop (𝓝 π') := by
  have hc := isContractionOn_hkOp hβ0 hβ1 hP hd
  obtain ⟨π', hπ', hfix⟩ := hc.exists_fixedPt isClosed_nonnegFns ⟨0, fun _ => le_rfl⟩
  exact ⟨π', hπ', hfix, fun π hπ h => hc.fixedPt_unique hπ hπ' h hfix,
    fun π hπ => hc.tendsto_iterate_fixedPt hπ hπ' hfix⟩

/-! ### Exercise 6.3.9: Blackwell's condition -/

/-- `T` is order preserving. -/
theorem hkOp_monotone {β : ℝ} (hβ : 0 ≤ β) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i))
    (d : X → ℝ) : Monotone (hkOp β P d) := by
  intro p q hpq x
  rw [hkOp_apply, hkOp_apply]
  refine Finset.sup'_mono_fun fun i _ => mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) hβ
  exact mul_le_mul_of_nonneg_right (add_le_add (hpq x') le_rfl) ((hP i).nonneg x x')

/-- `T(π + c) = Tπ + βc` for constants `c`, since each `Pᵢ𝟙 = 𝟙`. -/
theorem hkOp_add_const (β : ℝ) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i)) (d π : X → ℝ)
    (c : ℝ) : hkOp β P d (π + fun _ => c) = hkOp β P d π + fun _ => β * c := by
  funext x
  rw [Pi.add_apply, hkOp_apply, hkOp_apply]
  have h : ∀ i, β * ∑ x', ((π + fun _ : X => c) x' + d x') * P i x x' =
      β * ∑ x', (π x' + d x') * P i x x' + β * c := by
    intro i
    have h1 : ∑ x', ((π + fun _ : X => c) x' + d x') * P i x x' =
        ∑ x', (π x' + d x') * P i x x' + c * ∑ x', P i x x' := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun x' _ => by simp only [Pi.add_apply]; ring
    rw [h1, (hP i).rowsum, mul_one, mul_add]
  simp only [h]
  -- `max_i (f i + βc) = max_i f i + βc`
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i _ => add_le_add
      (Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x') (mem_univ i)) le_rfl
  · obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => β * ∑ x', (π x' + d x') * P i x x')
      univ_nonempty
    have hsup : (univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x') =
        β * ∑ x', (π x' + d x') * P i x x' :=
      le_antisymm (Finset.sup'_le _ _ fun j _ => hi j (mem_univ j))
        (Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x') (mem_univ i))
    rw [hsup]
    exact Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x' + β * c) (mem_univ i)

/-- Exercise 6.3.9 (p. 211): by Blackwell's condition (Lemma 2.2.4), `T` is a contraction of
modulus `β` on all of `ℝ^X`, hence on `ℝ^X₊`. -/
theorem isContractionOn_hkOp_univ {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ι → Matrix X X ℝ}
    (hP : ∀ i, IsMarkov (P i)) (d : X → ℝ) : IsContractionOn (hkOp β P d) Set.univ β :=
  isContractionOn_of_blackwell hβ0 hβ1 (hkOp_monotone hβ0 hP d) fun π c _ => by
    rw [hkOp_add_const β hP d π c]

end SargentStachurski.StochasticDiscounting

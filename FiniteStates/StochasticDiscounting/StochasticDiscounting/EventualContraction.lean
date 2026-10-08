/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.Valuation

/-!
# Eventual contractions

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.1.3 (pp. 189–192).

* A self-map `T` of `U` is eventually contracting if `Tᵏ` is a contraction on
  `U` for some `k` under some norm. Theorem 6.1.5 (Exercise 6.1.4): an
  eventual contraction on a closed set is globally stable. The fixed point of
  `Tᵏ` is fixed by `T`, since `T u*` is another fixed point of `Tᵏ`, and
  `‖Tⁿu − u*‖ ≤ L^{⌊n/k⌋} max_{r<k} ‖Tʳu − u*‖ → 0`.
* Exercise 6.1.5: if `Tᵏ` contracts under one norm then some `Tˡ` contracts
  under any equivalent norm. The equivalence constants, which exist for any two
  norms on `ℝ^X`, are hypotheses here.
* Example 6.1.2: `Tu = Au + b` with `ρ(A) < 1` is eventually contracting under
  the supremum norm, with fixed point `(I − A)⁻¹b`.
* Proposition 6.1.6: if `|Tv − Tw| ≤ L|v − w|` pointwise for a positive linear
  `L` with `ρ(L) < 1`, then `T` is eventually contracting.
* Proposition 6.1.7, the generalised Blackwell condition: an order-preserving
  `T` with `T(v + c) ≤ Tv + Lc` for `c ≥ 0` satisfies the hypothesis of
  Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Theorem 6.1.5 -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **Theorem 6.1.5** (p. 190), Exercise 6.1.4: if `T` maps the closed set `U` into itself and
`Tᵏ` is a contraction on `U` for some `k ≥ 1`, then `T` is globally stable on `U`: it has a unique
fixed point `u*` in `U`, and `Tⁿu → u*` for every `u ∈ U`. -/
theorem globallyStable_of_iterate_contraction [CompleteSpace E] {T : E → E} {U : Set E}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {k : ℕ} (hk : 0 < k) {L : ℝ}
    (hc : IsContractionOn (T^[k]) U L) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  obtain ⟨u', hu'U, hfix⟩ := hc.exists_fixedPt hU hne
  -- `T u'` is a fixed point of `Tᵏ` in `U`, hence equals `u'`
  have hTfix : IsFixedPt T u' := by
    have h1 : IsFixedPt (T^[k]) (T u') := by
      change T^[k] (T u') = T u'
      rw [← iterate_succ_apply, iterate_succ_apply', hfix.eq]
    exact hc.fixedPt_unique (hT hu'U) hu'U h1 hfix
  refine ⟨u', hu'U, hTfix, fun v hv hvfix => hc.fixedPt_unique hv hu'U (hvfix.iterate k) hfix,
    fun u hu => ?_⟩
  -- `Tⁿu = (Tᵏ)^{n/k}(T^{n%k}u)`, and `‖T^{n%k}u − u'‖ ≤ M := ∑_{r<k} ‖Tʳu − u'‖`
  set M : ℝ := ∑ r ∈ range k, ‖T^[r] u - u'‖ with hM
  have hM0 : 0 ≤ M := sum_nonneg fun _ _ => norm_nonneg _
  have hbound : ∀ n : ℕ, ‖T^[n] u - u'‖ ≤ L ^ (n / k) * M := by
    intro n
    have hn : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    have h1 : T^[n] u = (T^[k])^[n / k] (T^[n % k] u) := by
      conv_lhs => rw [hn]
      rw [iterate_add_apply, iterate_mul]
    rw [h1]
    have h2 := hc.norm_iterate_sub_fixedPt_le (hT.iterate (n % k) hu) hu'U hfix (n / k)
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc.nonneg _))
    exact single_le_sum (fun r _ => norm_nonneg (T^[r] u - u')) (mem_range.2 (Nat.mod_lt n hk))
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  have h3 : Tendsto (fun n : ℕ => L ^ (n / k)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.nonneg hc.lt_one).comp
      (Nat.tendsto_div_const_atTop hk.ne')
  simpa using h3.mul_const M

/-- Theorem 6.1.5 on the whole space, in the vocabulary of §1.2.2: an eventual contraction of
a complete space is globally stable. -/
theorem globallyStable_of_iterate_contraction_univ [CompleteSpace E] {T : E → E} {k : ℕ}
    (hk : 0 < k) {L : ℝ} (hc : IsContractionOn (T^[k]) Set.univ L) : GloballyStable T := by
  obtain ⟨u', -, hfix, huniq, hconv⟩ := globallyStable_of_iterate_contraction isClosed_univ
    ⟨0, Set.mem_univ 0⟩ (Set.mapsTo_univ T Set.univ) hk hc
  exact ⟨u', hfix, fun v hv => huniq v (Set.mem_univ v) hv, fun u => hconv u (Set.mem_univ u)⟩

/-! ### Exercise 6.1.5: changing the norm -/

omit [NormedAddCommGroup E] in
/-- Exercise 6.1.5 (p. 190): let `Nₐ, N_b` be two norms with `N_b ≤ c₂Nₐ` and `Nₐ ≤ c₁N_b` (any two
norms on `ℝ^X` are so related). If `Tᵏ` is a contraction on `U` under `Nₐ`, then some `Tˡ` is a
contraction on `U` under `N_b`: take `ℓ = km` with `c₂c₁Lᵐ < 1`. -/
theorem exists_iterate_contraction_of_norm_equiv [AddCommGroup E] (Na Nb : E → ℝ) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hba : ∀ u, Nb u ≤ c₂ * Na u) (hab : ∀ u, Na u ≤ c₁ * Nb u)
    {T : E → E} {U : Set E} (hT : Set.MapsTo T U U) {k : ℕ} {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hcon : ∀ u ∈ U, ∀ v ∈ U, Na (T^[k] u - T^[k] v) ≤ L * Na (u - v)) :
    ∃ ℓ : ℕ, ∃ L' : ℝ, 0 ≤ L' ∧ L' < 1 ∧
      ∀ u ∈ U, ∀ v ∈ U, Nb (T^[ℓ] u - T^[ℓ] v) ≤ L' * Nb (u - v) := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (c₂ * c₁) by positivity) hL1
  have hiter : ∀ (n : ℕ) (u : E), u ∈ U → ∀ v ∈ U,
      Na ((T^[k])^[n] u - (T^[k])^[n] v) ≤ L ^ n * Na (u - v) := by
    intro n
    induction n with
    | zero => intro u _ v _; simp
    | succ n ih =>
      intro u hu v hv
      rw [iterate_succ_apply', iterate_succ_apply']
      calc Na (T^[k] ((T^[k])^[n] u) - T^[k] ((T^[k])^[n] v))
          ≤ L * Na ((T^[k])^[n] u - (T^[k])^[n] v) :=
            hcon _ ((hT.iterate k).iterate n hu) _ ((hT.iterate k).iterate n hv)
        _ ≤ L * (L ^ n * Na (u - v)) := mul_le_mul_of_nonneg_left (ih u hu v hv) hL0
        _ = L ^ (n + 1) * Na (u - v) := by ring
  refine ⟨k * m, c₂ * c₁ * L ^ m, by positivity, ?_, fun u hu v hv => ?_⟩
  · have := (lt_div_iff₀ (by positivity)).1 hm
    linarith
  · rw [iterate_mul]
    calc Nb ((T^[k])^[m] u - (T^[k])^[m] v) ≤ c₂ * Na ((T^[k])^[m] u - (T^[k])^[m] v) := hba _
      _ ≤ c₂ * (L ^ m * Na (u - v)) := mul_le_mul_of_nonneg_left (hiter m u hu v hv) hc₂.le
      _ ≤ c₂ * (L ^ m * (c₁ * Nb (u - v))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hab _) ?_) hc₂.le
          positivity
      _ = c₂ * c₁ * L ^ m * Nb (u - v) := by ring

/-! ### Example 6.1.2: affine maps -/

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- The affine map `Tu = Au + b` of Example 6.1.2. -/
def affineOp (A : Matrix X X ℝ) (b : X → ℝ) (u : X → ℝ) : X → ℝ := A *ᵥ u + b

/-- `Tᵏu − Tᵏv = Aᵏ(u − v)`. -/
theorem affineOp_iterate_sub (A : Matrix X X ℝ) (b u v : X → ℝ) (k : ℕ) :
    (affineOp A b)^[k] u - (affineOp A b)^[k] v = A ^ k *ᵥ (u - v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', affineOp, affineOp, add_sub_add_right_eq_sub,
      ← mulVec_sub, ih, mulVec_mulVec, ← pow_succ']

/-- Example 6.1.2 (p. 190): if `ρ(A) < 1` then some `Tᵏ` is a contraction under the supremum
norm, with modulus `‖Aᵏ‖ < 1`. -/
theorem exists_isContractionOn_iterate_affineOp [Nonempty X] {A : Matrix X X ℝ}
    (hρ : specRad A < 1) (b : X → ℝ) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn ((affineOp A b)^[k]) Set.univ ‖A ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero A hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, Set.mapsTo_univ _ _, norm_nonneg _, hk1, fun u _ v _ => ?_⟩
  rw [affineOp_iterate_sub]
  exact Matrix.linfty_opNorm_mulVec _ _

omit [DecidableEq X] in
/-- Example 6.1.2 (p. 190): `Tu = Au + b` with `ρ(A) < 1` is globally stable, by Theorem 6.1.5. -/
theorem globallyStable_affineOp [Nonempty X] {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : GloballyStable (affineOp A b) := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_affineOp hρ b
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- Example 6.1.2 (p. 190): the fixed point is `(I − A)⁻¹b`, by the Neumann series lemma. -/
theorem isFixedPt_affineOp_inv [Nonempty X] {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : IsFixedPt (affineOp A b) ((1 - A)⁻¹ *ᵥ b) := by
  change A *ᵥ ((1 - A)⁻¹ *ᵥ b) + b = (1 - A)⁻¹ *ᵥ b
  rw [add_comm]
  exact (inv_mulVec_eq_add hρ b).symm

/-! ### Proposition 6.1.6: a spectral radius condition -/

omit [DecidableEq X] in
/-- A nonnegative matrix preserves `≤`. -/
theorem mulVec_le_mulVec_of_nonneg {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') {f g : X → ℝ}
    (hfg : f ≤ g) : L *ᵥ f ≤ L *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hL x x')

omit [DecidableEq X] in
/-- `‖|f|‖_∞ = ‖f‖_∞`. -/
theorem norm_abs_fun (f : X → ℝ) : ‖fun y => |f y|‖ = ‖f‖ := by
  simp only [Pi.norm_def, Real.nnnorm_abs]

omit [DecidableEq X] in
/-- If `|u| ≤ w` pointwise with `w ≥ 0`, then `‖u‖_∞ ≤ ‖w‖_∞`. -/
theorem norm_le_norm_of_abs_le_fun {u w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (h : ∀ x, |u x| ≤ w x) :
    ‖u‖ ≤ ‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  refine (h x).trans ?_
  have := norm_le_pi_norm w x
  rwa [Real.norm_eq_abs, abs_of_nonneg (hw x)] at this

/-- Iterating (6.13): `|Tᵏv − Tᵏw| ≤ Lᵏ|v − w|`, (6.14). -/
theorem abs_iterate_sub_le_pow_mulVec {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hT : Set.MapsTo T U U) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) (k : ℕ) :
    ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T^[k] v x - T^[k] w x| ≤ (L ^ k *ᵥ fun y => |v y - w y|) x := by
  induction k with
  | zero => intro v _ w _ x; simp
  | succ k ih =>
    intro v hv w hw x
    rw [iterate_succ_apply', iterate_succ_apply']
    refine (hdom _ (hT.iterate k hv) _ (hT.iterate k hw) x).trans ?_
    have h1 := mulVec_le_mulVec_of_nonneg hL (fun y => ih v hv w hw y) x
    rw [mulVec_mulVec, ← pow_succ'] at h1
    exact h1

/-- **Proposition 6.1.6** (p. 191): if `T` maps `U` into itself and `|Tv − Tw| ≤ L|v − w|` for a
positive linear `L` with `ρ(L) < 1`, then some `Tᵏ` is a contraction on `U` under the supremum norm,
with modulus `‖Lᵏ‖ < 1`. -/
theorem exists_isContractionOn_iterate_of_abs_sub_le [Nonempty X] {T : (X → ℝ) → (X → ℝ)}
    {U : Set (X → ℝ)} (hT : Set.MapsTo T U U) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (T^[k]) U ‖L ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero L hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, hT.iterate k, norm_nonneg _, hk1, fun v hv w hw => ?_⟩
  have hLk := pow_nonneg_entries hL k
  calc ‖T^[k] v - T^[k] w‖ ≤ ‖L ^ k *ᵥ fun y => |v y - w y|‖ :=
        norm_le_norm_of_abs_le_fun
          (fun x => sum_nonneg fun y _ => mul_nonneg (hLk x y) (abs_nonneg _))
          (abs_iterate_sub_le_pow_mulVec hT hL hdom k v hv w hw)
    _ ≤ ‖L ^ k‖ * ‖fun y => |v y - w y|‖ := Matrix.linfty_opNorm_mulVec _ _
    _ = ‖L ^ k‖ * ‖v - w‖ := by
        rw [show (fun y => |v y - w y|) = fun y => |(v - w) y| from rfl, norm_abs_fun]

omit [DecidableEq X] in
/-- Proposition 6.1.6 with Theorem 6.1.5: under (6.13) on a closed `U`, `T` is globally stable on
`U`. -/
theorem globallyStable_of_abs_sub_le [Nonempty X] {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {L : Matrix X X ℝ}
    (hL : ∀ x x', 0 ≤ L x x') (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_abs_sub_le hT hL hρ hdom
  exact globallyStable_of_iterate_contraction hU hne hT hk hc

/-! ### Proposition 6.1.7: a generalised Blackwell condition -/

omit [DecidableEq X] in
/-- **Proposition 6.1.7** (p. 191), the estimate: if `U` is closed under adding nonnegative
functions, `T` is order preserving on `U`, and `T(v + c) ≤ Tv + Lc` for `v ∈ U` and `c ≥ 0`, then
`|Tv − Tw| ≤ L|v − w|` on `U`. -/
theorem abs_sub_le_of_blackwell {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hU : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → v + c ∈ U)
    (hmono : ∀ v ∈ U, ∀ w ∈ U, v ≤ w → T v ≤ T w) {L : Matrix X X ℝ}
    (hdisc : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → T (v + c) ≤ T v + L *ᵥ c) :
    ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x := by
  have key : ∀ v ∈ U, ∀ w ∈ U, ∀ x, T v x - T w x ≤ (L *ᵥ fun y => |v y - w y|) x := by
    intro v hv w hw x
    have habs0 : (0 : X → ℝ) ≤ fun y => |v y - w y| := fun y => abs_nonneg _
    have hle : v ≤ w + fun y => |v y - w y| := fun y => by
      simp only [Pi.add_apply]
      linarith [le_abs_self (v y - w y)]
    have h1 := hmono v hv _ (hU w hw _ habs0) hle x
    have h2 := hdisc w hw _ habs0 x
    simp only [Pi.add_apply] at h1 h2
    linarith
  intro v hv w hw x
  rw [abs_sub_le_iff]
  refine ⟨key v hv w hw x, ?_⟩
  have := key w hw v hv x
  simpa [abs_sub_comm] using this

/-- **Proposition 6.1.7** (p. 191): under the generalised Blackwell condition with `ρ(L) < 1`, `T`
is eventually contracting on `U`. -/
theorem exists_isContractionOn_iterate_of_blackwell [Nonempty X] {T : (X → ℝ) → (X → ℝ)}
    {U : Set (X → ℝ)} (hT : Set.MapsTo T U U) (hU : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → v + c ∈ U)
    (hmono : ∀ v ∈ U, ∀ w ∈ U, v ≤ w → T v ≤ T w) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (hdisc : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → T (v + c) ≤ T v + L *ᵥ c) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (T^[k]) U ‖L ^ k‖ :=
  exists_isContractionOn_iterate_of_abs_sub_le hT hL hρ (abs_sub_le_of_blackwell hU hmono hdisc)

omit [DecidableEq X] in
/-- Proposition 6.1.7 with Theorem 6.1.5 on all of `ℝ^X`: an order-preserving `T` with
`T(v + c) ≤ Tv + Lc` for `c ≥ 0` and `ρ(L) < 1` is globally stable. -/
theorem globallyStable_of_blackwell [Nonempty X] {T : (X → ℝ) → (X → ℝ)} (hmono : Monotone T)
    {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (hρ : specRad L < 1)
    (hdisc : ∀ v : X → ℝ, ∀ c : X → ℝ, 0 ≤ c → T (v + c) ≤ T v + L *ᵥ c) :
    GloballyStable T := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_blackwell (Set.mapsTo_univ T Set.univ)
    (fun _ _ _ _ => Set.mem_univ _) (fun v _ w _ hvw => hmono hvw) hL hρ
    (fun v _ c hc => hdisc v c hc)
  exact globallyStable_of_iterate_contraction_univ hk hc

end SargentStachurski.StochasticDiscounting

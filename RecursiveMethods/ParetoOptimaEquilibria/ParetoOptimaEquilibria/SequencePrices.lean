/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.Economy

/-!
# Sequence spaces, truncations, and Lemma 15.5

SLP §15.4, pp. 463–464. `E` is a real normed space, the one-period commodity space (the book's
`X`). The commodity space is `S = BddSeq E`, the space of sequences `x = (x₀, x₁, …)` in `E` with
`‖x‖ = sup_t ‖x_t‖ < ∞` (Mathlib's `lp (fun _ : ℕ => E) ∞`).

* `seqTrunc T` (p. 463): the truncation `x ↦ xᵀ = (x₀, …, x_T, 0, 0, …)`, a continuous linear map
  of norm at most one (`norm_seqTrunc_le`), and `seqTrunc_eq_sum_single`: `xᵀ` is the sum of the
  coordinate vectors `x_t` placed in position `t`, `t ≤ T`.
* `seqC00`: the subspace of sequences that are eventually zero.
* `coordFunctional φ t` (`ψ_t`, p. 464): `φ` composed with the embedding of `E` as the `t`-th
  coordinate.
* `sum_abs_coordFunctional_le` (proof of Lemma 15.5): `Σ_{t<n} |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`.
* `seqRegularPart φ` (`ψ`, (1)–(2), p. 463): the continuous linear functional
  `ψ(x) = Σ_t ψ_t(x_t)`.
* **Lemma 15.5** (`lemma_15_5`, p. 463): `ψ(x) = lim_T φ(xᵀ)` for every `x`; the series
  `Σ_t ψ_t(x_t)` converges absolutely to `ψ(x)`, with `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`; `‖ψ‖ ≤ ‖φ‖`;
  `φ − ψ` vanishes on `seqC00`; and `ψ` itself has no weight at infinity, `ψ(x) = lim_T ψ(xᵀ)`.
* Inner product forms (3) (p. 464): for `E = ℝ`, `ψ(x) = Σ_t p_t x_t` with `Σ_t |p_t| ≤ ‖φ‖`
  (`seqRegularPart_real`); for `E = ℝᴷ` with the max norm, `ψ(x) = Σ_t Σ_k p_{tk} x_{tk}` with
  `Σ_t Σ_k |p_{tk}| ≤ ‖φ‖` (`seqRegularPart_euclid`).

**Correction.** None: Lemma 15.5 is correct. The book's case `x = θ` in the proof is unnecessary,
and the summability of the price sequence `(p_t)` in (3) is implicit in the book; it is proved here.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology
open scoped ENNReal

/-- The commodity space `S` of §15.4 (p. 463): bounded sequences in `E` with the sup norm. -/
abbrev BddSeq (E : Type*) [NormedAddCommGroup E] : Type _ := ↥(lp (fun _ : ℕ => E) ∞)

variable {E : Type*} [NormedAddCommGroup E]

/-- Coordinates of an element of `BddSeq E` are bounded by its norm. -/
theorem norm_seq_coord_le (x : BddSeq E) (t : ℕ) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x t

/-- An element of `BddSeq E` from a sequence bounded by `C ≥ 0`. -/
noncomputable def BddSeq.mk (f : ℕ → E) (C : ℝ) (hf : ∀ t, ‖f t‖ ≤ C) : BddSeq E :=
  ⟨f, memℓp_infty ⟨C, by rintro _ ⟨t, rfl⟩; exact hf t⟩⟩

/-- Coordinates of `BddSeq.mk`. -/
@[simp] theorem BddSeq.mk_apply (f : ℕ → E) (C : ℝ) (hf : ∀ t, ‖f t‖ ≤ C) (t : ℕ) :
    BddSeq.mk f C hf t = f t := rfl

/-- Coordinates of a finite sum of coordinate vectors. -/
theorem seq_sum_single_apply (s : Finset ℕ) (f : ℕ → E) (t : ℕ) :
    (∑ i ∈ s, lp.single ∞ i (f i) : BddSeq E) t = if t ∈ s then f t else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, lp.coeFn_add, Pi.add_apply, ih, lp.single_apply, Pi.single_apply]
    by_cases h : t = a
    · subst h; simp [ha]
    · simp [h]

variable [NormedSpace ℝ E]

/-- The truncation as a function: `xᵀ_t = x_t` for `t ≤ T` and `0` otherwise. -/
noncomputable def seqTruncFun (T : ℕ) (x : BddSeq E) : BddSeq E :=
  BddSeq.mk (fun t => if t ≤ T then x t else 0) ‖x‖ fun t => by
    split_ifs
    · exact norm_seq_coord_le x t
    · simp

omit [NormedSpace ℝ E] in
/-- The norm bound for truncations. -/
theorem norm_seqTruncFun_le (T : ℕ) (x : BddSeq E) : ‖seqTruncFun T x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg x) fun t => by
    change ‖(if t ≤ T then x t else 0)‖ ≤ ‖x‖
    split_ifs
    · exact norm_seq_coord_le x t
    · simp

/-- The **truncation** `x ↦ xᵀ = (x₀, …, x_T, 0, 0, …)` (p. 463), a continuous linear map. -/
noncomputable def seqTrunc (T : ℕ) : BddSeq E →L[ℝ] BddSeq E :=
  LinearMap.mkContinuous
    { toFun := seqTruncFun T
      map_add' := fun x y => by
        ext t
        change (if t ≤ T then (x + y) t else 0) =
          (if t ≤ T then x t else 0) + (if t ≤ T then y t else 0)
        split_ifs <;> simp
      map_smul' := fun c x => by
        ext t
        change (if t ≤ T then (c • x) t else 0) = c • (if t ≤ T then x t else 0)
        split_ifs <;> simp }
    1 fun x => by simpa using norm_seqTruncFun_le T x

/-- Coordinates of the truncation. -/
theorem seqTrunc_apply (T : ℕ) (x : BddSeq E) (t : ℕ) :
    seqTrunc T x t = if t ≤ T then x t else 0 := rfl

/-- Truncation does not increase the norm. -/
theorem norm_seqTrunc_le (T : ℕ) (x : BddSeq E) : ‖seqTrunc T x‖ ≤ ‖x‖ := norm_seqTruncFun_le T x

/-- The truncation is the sum of the coordinates placed in their positions:
`xᵀ = Σ_{t ≤ T} x̲_t`. -/
theorem seqTrunc_eq_sum_single (T : ℕ) (x : BddSeq E) :
    seqTrunc T x = ∑ t ∈ Finset.range (T + 1), lp.single ∞ t (x t) := by
  ext s
  rw [seqTrunc_apply, seq_sum_single_apply]
  simp

/-- Truncating twice truncates at the smaller index. -/
theorem seqTrunc_seqTrunc (T T' : ℕ) (x : BddSeq E) :
    seqTrunc T (seqTrunc T' x) = seqTrunc (min T T') x := by
  ext t
  simp only [seqTrunc_apply, le_min_iff]
  split_ifs <;> tauto

/-- The subspace `seqC00` of sequences that are eventually zero. -/
def seqC00 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Submodule ℝ (BddSeq E) where
  carrier := {x | ∀ᶠ t in atTop, x t = 0}
  add_mem' := fun hx hy => (hx.and hy).mono fun t h => by simp [h.1, h.2]
  zero_mem' := Eventually.of_forall fun t => rfl
  smul_mem' := fun c x hx => hx.mono fun t h => by simp [h]

/-- Truncations are eventually zero. -/
theorem seqTrunc_mem_seqC00 (T : ℕ) (x : BddSeq E) : seqTrunc T x ∈ seqC00 E :=
  (eventually_gt_atTop T).mono fun t ht => by simp [seqTrunc_apply, not_le.2 ht]

/-- An eventually zero sequence equals its truncations far enough out. -/
theorem eventually_seqTrunc_eq_of_mem_seqC00 {x : BddSeq E} (hx : x ∈ seqC00 E) :
    ∀ᶠ T in atTop, seqTrunc T x = x := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx
  filter_upwards [eventually_ge_atTop N] with T hT
  ext t
  rw [seqTrunc_apply]
  split_ifs with h
  · rfl
  · exact (hN t (hT.trans (not_le.1 h).le)).symm

/-- `ψ_t = φ ∘ (embedding of `E` as the `t`-th coordinate)` (p. 464). -/
noncomputable def coordFunctional (φ : StrongDual ℝ (BddSeq E)) (t : ℕ) : StrongDual ℝ E :=
  φ.comp (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => E) ∞ t)

/-- Value of `ψ_t`. -/
theorem coordFunctional_apply (φ : StrongDual ℝ (BddSeq E)) (t : ℕ) (a : E) :
    coordFunctional φ t a = φ (lp.single ∞ t a) := rfl

/-- `φ(xᵀ) = Σ_{t ≤ T} ψ_t(x_t)` (proof of Lemma 15.5). -/
theorem apply_seqTrunc_eq_sum (φ : StrongDual ℝ (BddSeq E)) (T : ℕ) (x : BddSeq E) :
    φ (seqTrunc T x) = ∑ t ∈ Finset.range (T + 1), coordFunctional φ t (x t) := by
  rw [seqTrunc_eq_sum_single, map_sum]
  rfl

/-- The key bound in the proof of Lemma 15.5: `Σ_{t<n} |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`. The book flips
the sign of each `x_t` so that every term is nonnegative and evaluates `φ` at the result. -/
theorem sum_abs_coordFunctional_le (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) (n : ℕ) :
    ∑ t ∈ Finset.range n, |coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖ := by
  set s : ℕ → ℝ := fun t => if 0 ≤ coordFunctional φ t (x t) then 1 else -1 with hs
  set y : BddSeq E := ∑ t ∈ Finset.range n, lp.single ∞ t (s t • x t) with hy
  have hsabs : ∀ t, ‖s t‖ = 1 := fun t => by simp only [hs]; split_ifs <;> simp
  have hyt : ∀ t, y t = if t ∈ Finset.range n then s t • x t else 0 := fun t => by
    rw [hy, seq_sum_single_apply]
  have hyn : ‖y‖ ≤ ‖x‖ := lp.norm_le_of_forall_le (norm_nonneg x) fun t => by
    rw [hyt]
    split_ifs
    · rw [norm_smul, hsabs, one_mul]; exact norm_seq_coord_le x t
    · simp
  have hφy : φ y = ∑ t ∈ Finset.range n, |coordFunctional φ t (x t)| := by
    rw [hy, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    change coordFunctional φ t (s t • x t) = _
    rw [map_smul, smul_eq_mul]
    simp only [hs]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  rw [← hφy]
  exact (le_abs_self _).trans ((φ.le_opNorm y).trans
    (mul_le_mul_of_nonneg_left hyn (norm_nonneg φ)))

/-- The series `Σ_t ψ_t(x_t)` converges absolutely. -/
theorem summable_abs_coordFunctional (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    Summable fun t => |coordFunctional φ t (x t)| :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) (sum_abs_coordFunctional_le φ x)

/-- The series `Σ_t ψ_t(x_t)` converges. -/
theorem summable_coordFunctional (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    Summable fun t => coordFunctional φ t (x t) :=
  (summable_abs_coordFunctional φ x).of_abs

/-- `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`. -/
theorem tsum_abs_coordFunctional_le (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    ∑' t, |coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖ :=
  Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) (sum_abs_coordFunctional_le φ x)

/-- `ψ` as a linear map. -/
noncomputable def seqRegularPartLinear (φ : StrongDual ℝ (BddSeq E)) : BddSeq E →ₗ[ℝ] ℝ where
  toFun x := ∑' t, coordFunctional φ t (x t)
  map_add' x y := by
    have h : ∀ t, coordFunctional φ t ((x + y) t) =
        coordFunctional φ t (x t) + coordFunctional φ t (y t) := fun t => by
      rw [lp.coeFn_add, Pi.add_apply, map_add]
    simp only [h]
    exact (summable_coordFunctional φ x).tsum_add (summable_coordFunctional φ y)
  map_smul' c x := by
    have h : ∀ t, coordFunctional φ t ((c • x) t) = c * coordFunctional φ t (x t) := fun t => by
      rw [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    simp only [h, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/-- `|ψ(x)| ≤ ‖φ‖ ‖x‖`. -/
theorem abs_seqRegularPartLinear_le (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    ‖seqRegularPartLinear φ x‖ ≤ ‖φ‖ * ‖x‖ := by
  have h := norm_tsum_le_tsum_norm (f := fun t => coordFunctional φ t (x t))
    (by simpa only [Real.norm_eq_abs] using summable_abs_coordFunctional φ x)
  simp only [Real.norm_eq_abs] at h
  change |∑' t, coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖
  exact h.trans (tsum_abs_coordFunctional_le φ x)

/-- The **regular part** `ψ` of `φ` ((1)–(2), p. 463): `ψ(x) = Σ_t ψ_t(x_t) = lim_T φ(xᵀ)`. -/
noncomputable def seqRegularPart (φ : StrongDual ℝ (BddSeq E)) : StrongDual ℝ (BddSeq E) :=
  (seqRegularPartLinear φ).mkContinuous ‖φ‖ (abs_seqRegularPartLinear_le φ)

/-- `ψ(x) = Σ'_t ψ_t(x_t)`. -/
theorem seqRegularPart_apply (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    seqRegularPart φ x = ∑' t, coordFunctional φ t (x t) := rfl

/-- (2): `ψ(x) = Σ_t ψ_t(x_t)`, as a `HasSum`. -/
theorem hasSum_seqRegularPart (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    HasSum (fun t => coordFunctional φ t (x t)) (seqRegularPart φ x) :=
  (summable_coordFunctional φ x).hasSum

/-- (1): `ψ(x) = lim_T φ(xᵀ)`. -/
theorem tendsto_apply_seqTrunc (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    Tendsto (fun T => φ (seqTrunc T x)) atTop (𝓝 (seqRegularPart φ x)) := by
  simp only [apply_seqTrunc_eq_sum]
  exact (hasSum_seqRegularPart φ x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- `‖ψ‖ ≤ ‖φ‖`. -/
theorem norm_seqRegularPart_le (φ : StrongDual ℝ (BddSeq E)) : ‖seqRegularPart φ‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg φ) _

/-- `φ − ψ` vanishes on eventually zero sequences. -/
theorem seqRegularPart_eq_of_mem_seqC00 (φ : StrongDual ℝ (BddSeq E)) {x : BddSeq E}
    (hx : x ∈ seqC00 E) : seqRegularPart φ x = φ x := by
  refine tendsto_nhds_unique (tendsto_apply_seqTrunc φ x) ?_
  exact tendsto_const_nhds.congr' ((eventually_seqTrunc_eq_of_mem_seqC00 hx).mono fun T h => by
    simp only [h])

/-- `ψ(xᵀ) = φ(xᵀ)`. -/
theorem seqRegularPart_seqTrunc (φ : StrongDual ℝ (BddSeq E)) (T : ℕ) (x : BddSeq E) :
    seqRegularPart φ (seqTrunc T x) = φ (seqTrunc T x) :=
  seqRegularPart_eq_of_mem_seqC00 φ (seqTrunc_mem_seqC00 T x)

/-- `ψ` has no weight at infinity: `ψ(x) = lim_T ψ(xᵀ)`, i.e. `ψ` is its own regular part. -/
theorem seqRegularPart_seqRegularPart (φ : StrongDual ℝ (BddSeq E)) :
    seqRegularPart (seqRegularPart φ) = seqRegularPart φ := by
  ext x
  refine tendsto_nhds_unique (tendsto_apply_seqTrunc (seqRegularPart φ) x) ?_
  simp only [seqRegularPart_seqTrunc]
  exact tendsto_apply_seqTrunc φ x

/-- **Lemma 15.5** (p. 463). For every `φ ∈ S*`, `ψ(x) = lim_T φ(xᵀ)` exists for every `x` and
defines `ψ ∈ S*` with `‖ψ‖ ≤ ‖φ‖`; `ψ(x) = Σ_t ψ_t(x_t)` with `ψ_t ∈ E*`, the series converging
absolutely with `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`; `φ − ψ` vanishes on the eventually zero sequences;
and `ψ(x) = lim_T ψ(xᵀ)`. -/
theorem lemma_15_5 (φ : StrongDual ℝ (BddSeq E)) :
    (∀ x : BddSeq E, Tendsto (fun T => φ (seqTrunc T x)) atTop (𝓝 (seqRegularPart φ x))) ∧
    (∀ x : BddSeq E, HasSum (fun t => coordFunctional φ t (x t)) (seqRegularPart φ x)) ∧
    (∀ x : BddSeq E, ∑' t, |coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖) ∧
    ‖seqRegularPart φ‖ ≤ ‖φ‖ ∧
    (∀ x ∈ seqC00 E, (φ - seqRegularPart φ) x = 0) ∧
    (∀ x : BddSeq E,
      Tendsto (fun T => seqRegularPart φ (seqTrunc T x)) atTop (𝓝 (seqRegularPart φ x))) :=
  ⟨tendsto_apply_seqTrunc φ, hasSum_seqRegularPart φ, tsum_abs_coordFunctional_le φ,
    norm_seqRegularPart_le φ, fun x hx => by simp [seqRegularPart_eq_of_mem_seqC00 φ hx],
    fun x => by
      simpa [seqRegularPart_seqRegularPart] using tendsto_apply_seqTrunc (seqRegularPart φ) x⟩

/-! ### Inner product forms (3) -/

/-- The constant sequence `1` in `ℓ∞`. -/
noncomputable def oneSeq : BddSeq ℝ := BddSeq.mk (fun _ => 1) 1 fun _ => by simp

/-- `‖1‖ ≤ 1` in `ℓ∞`. -/
theorem norm_oneSeq_le : ‖oneSeq‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun _ => by simp [oneSeq]

/-- (3) for `E = ℝ`: `ψ(x) = Σ_t p_t x_t` with `p_t = φ(e_t)` and `Σ_t |p_t| ≤ ‖φ‖`, so the price
sequence `p` is summable. -/
theorem seqRegularPart_real (φ : StrongDual ℝ (BddSeq ℝ)) :
    Summable (fun t => |φ (lp.single ∞ t 1)|) ∧ ∑' t, |φ (lp.single ∞ t 1)| ≤ ‖φ‖ ∧
    ∀ x : BddSeq ℝ, HasSum (fun t => φ (lp.single ∞ t 1) * x t) (seqRegularPart φ x) := by
  have hc : ∀ t (a : ℝ), coordFunctional φ t a = φ (lp.single ∞ t 1) * a := fun t a => by
    have : (lp.single ∞ t a : BddSeq ℝ) = a • (lp.single ∞ t 1 : BddSeq ℝ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [coordFunctional_apply, this, map_smul, smul_eq_mul, mul_comm]
  have h1 : ∀ t, |coordFunctional φ t (oneSeq t)| = |φ (lp.single ∞ t 1)| := fun t => by
    simp [hc, oneSeq]
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa only [h1] using summable_abs_coordFunctional φ oneSeq
  · have := tsum_abs_coordFunctional_le φ oneSeq
    simp only [h1] at this
    exact this.trans (mul_le_of_le_one_right (norm_nonneg φ) norm_oneSeq_le)
  · simpa only [hc] using hasSum_seqRegularPart φ x

/-- (3) for `E = ℝᴷ` with the max norm: `ψ(x) = Σ_t Σ_k p_{tk} x_{tk}` with
`p_{tk} = φ(e_t ⊗ e_k)` and `Σ_t Σ_k |p_{tk}| ≤ ‖φ‖`. -/
theorem seqRegularPart_euclid {K : ℕ} (φ : StrongDual ℝ (BddSeq (Fin K → ℝ))) :
    Summable (fun t => ∑ k, |φ (lp.single ∞ t (Pi.single k 1))|) ∧
    ∑' t, ∑ k, |φ (lp.single ∞ t (Pi.single k 1))| ≤ ‖φ‖ ∧
    ∀ x : BddSeq (Fin K → ℝ),
      HasSum (fun t => ∑ k, φ (lp.single ∞ t (Pi.single k 1)) * x t k) (seqRegularPart φ x) := by
  set p : ℕ → Fin K → ℝ := fun t k => φ (lp.single ∞ t (Pi.single k 1)) with hp
  have hc : ∀ t (a : Fin K → ℝ), coordFunctional φ t a = ∑ k, p t k * a k := fun t a => by
    have ha : a = ∑ k, a k • (Pi.single k 1 : Fin K → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  set sgn : ℕ → Fin K → ℝ := fun t k => if 0 ≤ p t k then 1 else -1 with hsgn
  have hsgn1 : ∀ t, ‖sgn t‖ ≤ 1 := fun t =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by
      simp only [hsgn]; split_ifs <;> simp
  set z : BddSeq (Fin K → ℝ) := BddSeq.mk sgn 1 hsgn1 with hz
  have hzn : ‖z‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one fun t => hsgn1 t
  have habs : ∀ t, |coordFunctional φ t (z t)| = ∑ k, |p t k| := fun t => by
    have : coordFunctional φ t (z t) = ∑ k, |p t k| := by
      rw [hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hz, BddSeq.mk_apply, hsgn]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [abs_of_neg (not_le.1 h)]; ring
    rw [this, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)]
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa only [habs] using summable_abs_coordFunctional φ z
  · have := tsum_abs_coordFunctional_le φ z
    simp only [habs] at this
    exact this.trans (mul_le_of_le_one_right (norm_nonneg φ) hzn)
  · simpa only [hc] using hasSum_seqRegularPart φ x

end StokeyLucasPrescott.ParetoOptimaEquilibria

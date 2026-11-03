/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.Owen1DLindeberg
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite product spaces: independence, moments, and a conditional Lindeberg bound

Tools for Loh's (2003) CLT for non-additive integrands (post #2). A nested scramble is a
function `ρ : Γ → P` from the nodes of a tree to the permutations of the digits, and the uniform
scramble is the uniform law on these functions, under which the node permutations are
independent. This module proves what that independence gives on a finite product space, with
the uniform average `unifAvg` in place of the expectation.

## Main results

* `unifAvg_mul_of_disjoint`: functions of disjoint sets of coordinates are uncorrelated
  (independent).
* `unifAvg_eval`, `unifAvg_prod`: one coordinate is uniform; the average of a product of
  functions of distinct coordinates is the product of the averages.
* `unifAvg_sq_sum_eq`, `unifAvg_pow_four_sum_le`: for centred terms of distinct coordinates,
  `E[(Σ X_j)²] = Σ E[X_j²]` and `E[(Σ X_j)⁴] ≤ 3 (Σ β_j²)²` when `|X_j| ≤ β_j`.
* `sum_perm_apply`: under a uniform permutation every point has a uniform image.
* `norm_unifAvg_cexp_sub_le`: the cubic bound for the characteristic function of a bounded
  centred variable on a finite uniform space.
* `sq_unifAvg_sum_mul_le`: Cauchy–Schwarz for averages of finite sums.
* `tendsto_unifAvg_cexp_nodeSum` (**conditional Lindeberg CLT, Lyapunov form**): for each `m`
  let `ξ m r γ π` be centred node terms, indexed by an outer variable `r` and the nodes `γ`, with
  `|ξ m r γ π| ≤ M m r γ`, and let `T = Σ_γ ξ m r γ (ρ γ)` with `ρ` uniform. If the conditional
  variances `V(r) = Σ_γ E_π ξ²` satisfy `E_r |V(r)/s² - 1| → 0`, `E_r Σ_γ (M/s)²` stays bounded
  and `E_r Σ_γ (M/s)⁴ → 0`, then the characteristic function of `T / s` at `τ_m → t` tends to
  `e^{-t²/2}`. This is the CLT for sums that are, conditionally on `r`, sums of independent
  terms, with a random conditional variance that concentrates.
-/

namespace RQMCMarkov.OwenScrambling

open Finset Filter Complex
open scoped Topology

/-- The uniform average `(#α)⁻¹ Σ_a F a` of a function on a finite type. -/
noncomputable def unifAvg {α : Type*} [Fintype α] {𝕜 : Type*} [DivisionRing 𝕜] (F : α → 𝕜) :
    𝕜 :=
  (Fintype.card α : 𝕜)⁻¹ * ∑ a, F a

/-- The average is additive. -/
theorem unifAvg_add {α : Type*} [Fintype α] (F G : α → ℝ) :
    unifAvg (fun a ↦ F a + G a) = unifAvg F + unifAvg G := by
  unfold unifAvg
  rw [Finset.sum_add_distrib, mul_add]

/-- The average commutes with multiplication by a constant. -/
theorem unifAvg_const_mul {α : Type*} [Fintype α] (c : ℝ) (F : α → ℝ) :
    unifAvg (fun a ↦ c * F a) = c * unifAvg F := by
  unfold unifAvg
  rw [← Finset.mul_sum]
  ring

/-- The average commutes with multiplication by a constant on the right. -/
theorem unifAvg_mul_const {α : Type*} [Fintype α] (F : α → ℝ) (c : ℝ) :
    unifAvg (fun a ↦ F a * c) = unifAvg F * c := by
  unfold unifAvg
  rw [← Finset.sum_mul]
  ring

/-- The average of a constant. -/
theorem unifAvg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    unifAvg (fun _ : α ↦ c) = c := by
  unfold unifAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The average is monotone. -/
theorem unifAvg_mono {α : Type*} [Fintype α] {F G : α → ℝ} (h : ∀ a, F a ≤ G a) :
    unifAvg F ≤ unifAvg G := by
  unfold unifAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ ↦ h a)
    (inv_nonneg.2 (Nat.cast_nonneg _))

/-- The average of a nonnegative function is nonnegative. -/
theorem unifAvg_nonneg {α : Type*} [Fintype α] {F : α → ℝ} (h : ∀ a, 0 ≤ F a) :
    0 ≤ unifAvg F := by
  unfold unifAvg
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun a _ ↦ h a)

/-- The average of a finite sum of functions. -/
theorem unifAvg_sum {α ι : Type*} [Fintype α] (s : Finset ι) (F : ι → α → ℝ) :
    unifAvg (fun a ↦ ∑ i ∈ s, F i a) = ∑ i ∈ s, unifAvg (F i) := by
  unfold unifAvg
  rw [Finset.sum_comm, Finset.mul_sum]

/-- `|E F| ≤ E |F|`. -/
theorem abs_unifAvg_le {α : Type*} [Fintype α] (F : α → ℝ) :
    |unifAvg F| ≤ unifAvg fun a ↦ |F a| := by
  unfold unifAvg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.2 (Nat.cast_nonneg _))

/-- **Cauchy–Schwarz** for averages: `(E[F G])² ≤ E[F²] E[G²]`. -/
theorem sq_unifAvg_mul_le {α : Type*} [Fintype α] (F G : α → ℝ) :
    (unifAvg fun a ↦ F a * G a) ^ 2 ≤ (unifAvg fun a ↦ F a ^ 2) * unifAvg fun a ↦ G a ^ 2 := by
  unfold unifAvg
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  have hc : (0 : ℝ) ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((Fintype.card α : ℝ)⁻¹ * ∑ a, F a * G a) ^ 2
      = ((Fintype.card α : ℝ)⁻¹) ^ 2 * (∑ a, F a * G a) ^ 2 := by ring
    _ ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 * ((∑ a, F a ^ 2) * ∑ a, G a ^ 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

/-- **Jensen** for averages: `(E F)² ≤ E[F²]`. -/
theorem sq_unifAvg_le {α : Type*} [Fintype α] (F : α → ℝ) :
    (unifAvg F) ^ 2 ≤ unifAvg fun a ↦ F a ^ 2 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · unfold unifAvg
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty]
    simp
  have h := sq_unifAvg_mul_le F (fun _ ↦ 1)
  simp only [mul_one, one_pow] at h
  rw [unifAvg_const] at h
  linarith

/-- **Functions of disjoint sets of coordinates are independent** under the uniform law on
`Γ → P`: if `F` depends only on the coordinates in `p` and `G` only on those outside `p`, then
`E[F G] = E[F] E[G]`. -/
theorem unifAvg_mul_of_disjoint {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    [Nonempty P]
    (p : Γ → Prop) {F G : (Γ → P) → ℝ}
    (hF : ∀ ρ ρ' : Γ → P, (∀ γ, p γ → ρ γ = ρ' γ) → F ρ = F ρ')
    (hG : ∀ ρ ρ' : Γ → P, (∀ γ, ¬ p γ → ρ γ = ρ' γ) → G ρ = G ρ') :
    unifAvg (fun ρ ↦ F ρ * G ρ) = unifAvg F * unifAvg G := by
  classical
  set e := Equiv.piEquivPiSubtypeProd p (fun _ : Γ ↦ P) with he
  obtain ⟨pm₀⟩ := ‹Nonempty P›
  set a₀ : ∀ _ : {x // p x}, P := fun _ ↦ pm₀
  set c₀ : ∀ _ : {x // ¬ p x}, P := fun _ ↦ pm₀
  have hFe : ∀ a c, F (e.symm (a, c)) = F (e.symm (a, c₀)) := fun a c ↦ hF _ _ fun γ hγ ↦ by
    simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, hγ]
  have hGe : ∀ a c, G (e.symm (a, c)) = G (e.symm (a₀, c)) := fun a c ↦ hG _ _ fun γ hγ ↦ by
    simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, hγ]
  have hsum : ∀ H : (Γ → P) → ℝ, ∑ ρ, H ρ = ∑ a, ∑ c, H (e.symm (a, c)) := fun H ↦ by
    rw [← Fintype.sum_prod_type (f := fun q ↦ H (e.symm q))]
    exact (Fintype.sum_equiv e.symm (fun q ↦ H (e.symm q)) H fun _ ↦ rfl).symm
  have hcard : (Fintype.card (Γ → P) : ℝ) = (Fintype.card (∀ _ : {x // p x}, P) : ℝ) *
      (Fintype.card (∀ _ : {x // ¬ p x}, P) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  set A := (Fintype.card (∀ _ : {x // p x}, P) : ℝ)
  set C := (Fintype.card (∀ _ : {x // ¬ p x}, P) : ℝ)
  have hA : A ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hC : C ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ ρ, F ρ * G ρ = (∑ a, F (e.symm (a, c₀))) * ∑ c, G (e.symm (a₀, c)) := by
    rw [hsum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ by rw [hFe, hGe]
  have e2 : ∑ ρ, F ρ = C * ∑ a, F (e.symm (a, c₀)) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_congr rfl fun c _ ↦ hFe a c, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have e3 : ∑ ρ, G ρ = A * ∑ c, G (e.symm (a₀, c)) := by
    rw [hsum, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.sum_congr rfl fun a _ ↦ hGe a c, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  unfold unifAvg
  rw [e1, e2, e3, hcard]
  field_simp

/-- **One coordinate of a uniform function is uniform**: `E[h(ρ γ)] = E_π[h π]`. -/
theorem unifAvg_eval {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P] (γ : Γ)
    (h : P → ℝ) : unifAvg (fun ρ : Γ → P ↦ h (ρ γ)) = unifAvg h := by
  set e := Equiv.funSplitAt γ P with he
  have hs : ∑ ρ : Γ → P, h (ρ γ) = ∑ q : P × ({j // j ≠ γ} → P), h q.1 :=
    Fintype.sum_equiv e _ _ fun ρ ↦ rfl
  have hcard : (Fintype.card (Γ → P) : ℝ) =
      (Fintype.card P : ℝ) * (Fintype.card ({j // j ≠ γ} → P) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  unfold unifAvg
  rw [hs, Fintype.sum_prod_type, hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rcases isEmpty_or_nonempty ({j // j ≠ γ} → P) with hR | hR
  · rcases isEmpty_or_nonempty P with hP | hP
    · simp [Finset.univ_eq_empty]
    · exact absurd hR (not_isEmpty_of_nonempty _)
  · have : (Fintype.card ({j // j ≠ γ} → P) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [mul_inv]
    field_simp

/-- **The average of a product of functions of distinct coordinates** is the product of their
averages (complex-valued). -/
theorem unifAvg_prod {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P] (g : Γ → P → ℂ) :
    unifAvg (fun ρ : Γ → P ↦ ∏ γ, g γ (ρ γ)) = ∏ γ, unifAvg (g γ) := by
  unfold unifAvg
  rw [Finset.prod_mul_distrib, ← Fintype.prod_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow, inv_pow]

/-- **One coordinate is independent of functions of the others**:
`E[h(ρ γ) G(ρ)] = E_π[h π] E[G]` when `G` does not depend on coordinate `γ`. -/
theorem unifAvg_mul_eval_of_forall_ne {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    [Nonempty P] (γ : Γ) (h : P → ℝ) {G : (Γ → P) → ℝ}
    (hG : ∀ ρ ρ' : Γ → P, (∀ γ', ¬ γ' = γ → ρ γ' = ρ' γ') → G ρ = G ρ') :
    unifAvg (fun ρ ↦ h (ρ γ) * G ρ) = unifAvg h * unifAvg G := by
  rw [unifAvg_mul_of_disjoint (fun γ' ↦ γ' = γ) (F := fun ρ ↦ h (ρ γ))
    (fun ρ ρ' hρ ↦ by rw [hρ γ rfl]) hG, unifAvg_eval]

/-- A sum of terms of coordinates other than `γ` does not depend on coordinate `γ`. -/
theorem sum_eval_congr {Γ P ι : Type*} {J : Finset ι} {ν : ι → Γ} {γ : Γ}
    (hJ : ∀ j ∈ J, ν j ≠ γ) (X : ι → P → ℝ) (ρ ρ' : Γ → P)
    (h : ∀ γ', ¬ γ' = γ → ρ γ' = ρ' γ') :
    ∑ j ∈ J, X j (ρ (ν j)) = ∑ j ∈ J, X j (ρ' (ν j)) :=
  Finset.sum_congr rfl fun j hj ↦ by rw [h _ (hJ j hj)]

/-- The average of a sum of coordinate terms is the sum of their averages. -/
theorem unifAvg_sum_eval {Γ P ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    (J : Finset ι) (ν : ι → Γ) (X : ι → P → ℝ) :
    unifAvg (fun ρ : Γ → P ↦ ∑ j ∈ J, X j (ρ (ν j))) = ∑ j ∈ J, unifAvg (X j) := by
  rw [unifAvg_sum]
  exact Finset.sum_congr rfl fun j _ ↦ unifAvg_eval (ν j) (X j)

/-- Injectivity on `insert j₀ J` separates `ν j₀` from `ν '' J`. -/
theorem ne_of_injOn_insert {Γ ι : Type*} [DecidableEq ι] {J : Finset ι} {j₀ : ι} {ν : ι → Γ}
    (hν : Set.InjOn ν ↑(insert j₀ J)) (hj₀ : j₀ ∉ J) : ∀ j ∈ J, ν j ≠ ν j₀ := by
  intro j hj heq
  have := hν (Finset.mem_coe.2 (Finset.mem_insert_of_mem hj))
    (Finset.mem_coe.2 (Finset.mem_insert_self j₀ J)) heq
  rw [this] at hj
  exact hj₀ hj

/-- Injectivity on `insert j₀ J` gives injectivity on `J`. -/
theorem injOn_of_insert {Γ ι : Type*} [DecidableEq ι] {J : Finset ι} {j₀ : ι} {ν : ι → Γ}
    (hν : Set.InjOn ν ↑(insert j₀ J)) : Set.InjOn ν ↑J :=
  hν.mono fun _ hj ↦ Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hj))

/-- **Second moment of a sum of centred terms of distinct coordinates**:
`E[(Σ_{j ∈ J} X_j(ρ(ν j)))²] = Σ_{j ∈ J} E_π[X_j²]` when `ν` is injective on `J`. -/
theorem unifAvg_sq_sum_eq {Γ P ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P] [Nonempty P]
    {J : Finset ι} {ν : ι → Γ} (hν : Set.InjOn ν ↑J) {X : ι → P → ℝ}
    (h0 : ∀ j ∈ J, unifAvg (X j) = 0) :
    unifAvg (fun ρ : Γ → P ↦ (∑ j ∈ J, X j (ρ (ν j))) ^ 2) =
      ∑ j ∈ J, unifAvg (fun pm ↦ X j pm ^ 2) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : Γ → P ↦ (0 : ℝ) ^ 2) = fun _ ↦ 0 from funext fun _ ↦ by ring,
        unifAvg_const]
  | insert j₀ J hj₀ ih =>
      have hne := ne_of_injOn_insert hν hj₀
      have hS0 : ∀ j ∈ J, unifAvg (X j) = 0 := fun j hj ↦ h0 j (Finset.mem_insert_of_mem hj)
      have hX0 := h0 j₀ (Finset.mem_insert_self j₀ J)
      rw [Finset.sum_insert hj₀]
      simp only [Finset.sum_insert hj₀]
      have e : (fun ρ : Γ → P ↦ (X j₀ (ρ (ν j₀)) + ∑ j ∈ J, X j (ρ (ν j))) ^ 2) =
          fun ρ ↦ (X j₀ (ρ (ν j₀)) ^ 2 + 2 * (X j₀ (ρ (ν j₀)) * ∑ j ∈ J, X j (ρ (ν j)))) +
            (∑ j ∈ J, X j (ρ (ν j))) ^ 2 := funext fun ρ ↦ by ring
      rw [e, unifAvg_add, unifAvg_add, unifAvg_const_mul,
        unifAvg_mul_eval_of_forall_ne (ν j₀) (X j₀) (sum_eval_congr hne X), hX0, zero_mul,
        mul_zero, add_zero, ih (injOn_of_insert hν) hS0,
        unifAvg_eval (ν j₀) (fun pm ↦ X j₀ pm ^ 2)]

/-- **Fourth moment of a sum of centred bounded terms of distinct coordinates**:
`E[(Σ_{j ∈ J} X_j(ρ(ν j)))⁴] ≤ 3 (Σ_{j ∈ J} β_j²)²` when `|X_j| ≤ β_j` and `ν` is injective
on `J`. -/
theorem unifAvg_pow_four_sum_le {Γ P ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    [Nonempty P] {J : Finset ι} {ν : ι → Γ} (hν : Set.InjOn ν ↑J) {X : ι → P → ℝ}
    (h0 : ∀ j ∈ J, unifAvg (X j) = 0) {β : ι → ℝ} (hβ : ∀ j ∈ J, ∀ pm, |X j pm| ≤ β j) :
    unifAvg (fun ρ : Γ → P ↦ (∑ j ∈ J, X j (ρ (ν j))) ^ 4) ≤ 3 * (∑ j ∈ J, β j ^ 2) ^ 2 := by
  classical
  obtain ⟨pm₀⟩ := ‹Nonempty P›
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : Γ → P ↦ (0 : ℝ) ^ 4) = fun _ ↦ 0 from funext fun _ ↦ by ring,
        unifAvg_const]
      norm_num
  | insert j₀ J hj₀ ih =>
      have hne := ne_of_injOn_insert hν hj₀
      have hνJ := injOn_of_insert hν
      have hS0 : ∀ j ∈ J, unifAvg (X j) = 0 := fun j hj ↦ h0 j (Finset.mem_insert_of_mem hj)
      have hβJ : ∀ j ∈ J, ∀ pm, |X j pm| ≤ β j := fun j hj ↦ hβ j (Finset.mem_insert_of_mem hj)
      have hX0 := h0 j₀ (Finset.mem_insert_self j₀ J)
      have hβ0 := hβ j₀ (Finset.mem_insert_self j₀ J)
      set S : (Γ → P) → ℝ := fun ρ ↦ ∑ j ∈ J, X j (ρ (ν j)) with hS
      set a : (Γ → P) → ℝ := fun ρ ↦ X j₀ (ρ (ν j₀)) with ha
      set B := ∑ j ∈ J, β j ^ 2 with hB
      have hcong : ∀ k : ℕ, ∀ ρ ρ' : Γ → P, (∀ γ', ¬ γ' = ν j₀ → ρ γ' = ρ' γ') →
          S ρ ^ k = S ρ' ^ k := fun k ρ ρ' h ↦ by
        change (∑ j ∈ J, X j (ρ (ν j))) ^ k = (∑ j ∈ J, X j (ρ' (ν j))) ^ k
        rw [sum_eval_congr hne X ρ ρ' h]
      have hind : ∀ k l : ℕ, unifAvg (fun ρ ↦ a ρ ^ k * S ρ ^ l) =
          unifAvg (fun pm ↦ X j₀ pm ^ k) * unifAvg (fun ρ ↦ S ρ ^ l) := fun k l ↦
        unifAvg_mul_eval_of_forall_ne (ν j₀) (fun pm ↦ X j₀ pm ^ k) (hcong l)
      have hS1 : unifAvg S = 0 := by
        rw [hS, unifAvg_sum_eval, Finset.sum_eq_zero hS0]
      have hS2 : unifAvg (fun ρ ↦ S ρ ^ 2) ≤ B := by
        rw [hS, unifAvg_sq_sum_eq hνJ hS0, hB]
        refine Finset.sum_le_sum fun j hj ↦ ?_
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hβJ j hj pm) 2
      have hβ0nn : 0 ≤ β j₀ := (abs_nonneg _).trans (hβ0 pm₀)
      have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      have ha2 : unifAvg (fun pm ↦ X j₀ pm ^ 2) ≤ β j₀ ^ 2 := by
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hβ0 pm) 2
      have ha4 : unifAvg (fun pm ↦ X j₀ pm ^ 4) ≤ β j₀ ^ 4 := by
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [show X j₀ pm ^ 4 = |X j₀ pm| ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
        exact pow_le_pow_left₀ (abs_nonneg _) (hβ0 pm) 4
      have ha2nn : 0 ≤ unifAvg (fun pm ↦ X j₀ pm ^ 2) := unifAvg_nonneg fun pm ↦ sq_nonneg _
      have hS2nn : 0 ≤ unifAvg (fun ρ ↦ S ρ ^ 2) := unifAvg_nonneg fun ρ ↦ sq_nonneg _
      have hS4 := ih hνJ hS0 hβJ
      rw [Finset.sum_insert hj₀]
      simp only [Finset.sum_insert hj₀]
      have e : (fun ρ : Γ → P ↦ (X j₀ (ρ (ν j₀)) + ∑ j ∈ J, X j (ρ (ν j))) ^ 4) =
          fun ρ ↦ (((a ρ ^ 4 * S ρ ^ 0 + 4 * (a ρ ^ 3 * S ρ ^ 1)) +
            6 * (a ρ ^ 2 * S ρ ^ 2)) + 4 * (a ρ ^ 1 * S ρ ^ 3)) + S ρ ^ 4 :=
        funext fun ρ ↦ by rw [ha, hS]; ring
      rw [e, unifAvg_add, unifAvg_add, unifAvg_add, unifAvg_add, unifAvg_const_mul,
        unifAvg_const_mul, unifAvg_const_mul, hind, hind, hind, hind]
      have h1 : unifAvg (fun ρ ↦ S ρ ^ 1) = 0 := by simpa only [pow_one] using hS1
      have h0' : unifAvg (fun pm ↦ X j₀ pm ^ 1) = 0 := by simpa only [pow_one] using hX0
      have hc0 : unifAvg (fun ρ ↦ S ρ ^ 0) = 1 := by
        simp only [pow_zero]
        exact unifAvg_const 1
      rw [h1, h0', hc0]
      have hS4' : unifAvg (fun ρ ↦ S ρ ^ 4) ≤ 3 * B ^ 2 := hS4
      have hm : unifAvg (fun pm ↦ X j₀ pm ^ 2) * unifAvg (fun ρ ↦ S ρ ^ 2) ≤ β j₀ ^ 2 * B :=
        mul_le_mul ha2 hS2 hS2nn (sq_nonneg _)
      nlinarith [sq_nonneg (β j₀), pow_nonneg hβ0nn 4, mul_nonneg (sq_nonneg (β j₀)) hB0]

/-- **Under a uniform permutation each point has a uniform image**:
`#α · Σ_π g(π c) = #Perm(α) · Σ_a g a`. -/
theorem sum_perm_apply {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℝ) (c : α) :
    (Fintype.card α : ℝ) * ∑ pm : Equiv.Perm α, g (pm c) =
      (Fintype.card (Equiv.Perm α) : ℝ) * ∑ a, g a := by
  have hT : ∀ x y : α, ∑ pm : Equiv.Perm α, g (pm x) = ∑ pm : Equiv.Perm α, g (pm y) :=
    fun x y ↦ Fintype.sum_equiv (Equiv.mulRight (Equiv.swap x y)) _ _ fun pm ↦ by
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  calc (Fintype.card α : ℝ) * ∑ pm : Equiv.Perm α, g (pm c)
      = ∑ x : α, ∑ pm : Equiv.Perm α, g (pm x) := by
        rw [Finset.sum_congr rfl fun x _ ↦ hT x c, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ = ∑ pm : Equiv.Perm α, ∑ x : α, g (pm x) := Finset.sum_comm
    _ = ∑ pm : Equiv.Perm α, ∑ a, g a := Finset.sum_congr rfl fun pm _ ↦ Equiv.sum_comp pm g
    _ = (Fintype.card (Equiv.Perm α) : ℝ) * ∑ a, g a := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The norm of a complex average is at most the average of the norms. -/
theorem norm_unifAvg_le {α : Type*} [Fintype α] (F : α → ℂ) :
    ‖unifAvg F‖ ≤ unifAvg fun a ↦ ‖F a‖ := by
  unfold unifAvg
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 (Nat.cast_nonneg _))

/-- Complex averages are additive under subtraction. -/
theorem unifAvg_sub_complex {α : Type*} [Fintype α] (F G : α → ℂ) :
    unifAvg (fun a ↦ F a - G a) = unifAvg F - unifAvg G := by
  unfold unifAvg
  rw [Finset.sum_sub_distrib, mul_sub]

/-- The average of a complex constant. -/
theorem unifAvg_const_complex {α : Type*} [Fintype α] [Nonempty α] (c : ℂ) :
    unifAvg (fun _ : α ↦ c) = c := by
  unfold unifAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The complex average of real values is the real average. -/
theorem unifAvg_ofReal {α : Type*} [Fintype α] (F : α → ℝ) :
    unifAvg (fun a ↦ (F a : ℂ)) = ((unifAvg F : ℝ) : ℂ) := by
  unfold unifAvg
  push_cast
  rfl

/-- **The characteristic function of a bounded centred variable on a finite uniform space**:
if `E X = 0`, `|X| ≤ δ` and `|t| δ ≤ 1`, then
`‖E e^{itX} - (1 - t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`. -/
theorem norm_unifAvg_cexp_sub_le {P : Type*} [Fintype P] [Nonempty P] {X : P → ℝ}
    (h0 : unifAvg X = 0) {δ : ℝ} (hX : ∀ pm, |X pm| ≤ δ) {t : ℝ} (ht : |t| * δ ≤ 1) :
    ‖unifAvg (fun pm ↦ cexp (((t * X pm : ℝ) : ℂ) * I)) -
        (((1 - t ^ 2 * unifAvg (fun pm ↦ X pm ^ 2) / 2 : ℝ)) : ℂ)‖ ≤
      |t| ^ 3 * δ * unifAvg (fun pm ↦ X pm ^ 2) := by
  set q : P → ℂ := fun pm ↦ (((1 - (t * X pm) ^ 2 / 2 : ℝ)) : ℂ) + ((t * X pm : ℝ) : ℂ) * I
    with hq
  have hqa : unifAvg q = (((1 - t ^ 2 * unifAvg (fun pm ↦ X pm ^ 2) / 2 : ℝ)) : ℂ) := by
    have e1 : q = fun pm ↦ (((1 - t ^ 2 / 2 * X pm ^ 2 : ℝ)) : ℂ) + ((t * X pm : ℝ) : ℂ) * I :=
      funext fun pm ↦ by rw [hq]; push_cast; ring
    have e2 : unifAvg (fun pm ↦ (((1 - t ^ 2 / 2 * X pm ^ 2 : ℝ)) : ℂ)) =
        (((1 - t ^ 2 * unifAvg (fun pm ↦ X pm ^ 2) / 2 : ℝ)) : ℂ) := by
      rw [unifAvg_ofReal]
      congr 1
      rw [show (fun pm ↦ 1 - t ^ 2 / 2 * X pm ^ 2) = fun pm ↦ 1 + (-(t ^ 2 / 2)) * X pm ^ 2 from
        funext fun pm ↦ by ring, unifAvg_add, unifAvg_const, unifAvg_const_mul]
      ring
    have e3 : unifAvg (fun pm ↦ ((t * X pm : ℝ) : ℂ) * I) = 0 := by
      have : unifAvg (fun pm ↦ ((t * X pm : ℝ) : ℂ) * I) =
          unifAvg (fun pm ↦ ((t * X pm : ℝ) : ℂ)) * I := by
        unfold unifAvg
        rw [← Finset.sum_mul, mul_assoc]
      rw [this, unifAvg_ofReal, unifAvg_const_mul, h0, mul_zero, Complex.ofReal_zero, zero_mul]
    rw [e1]
    unfold unifAvg at e2 e3 ⊢
    rw [Finset.sum_add_distrib, mul_add, e2, e3, add_zero]
  rw [← hqa, ← unifAvg_sub_complex]
  refine (norm_unifAvg_le _).trans ?_
  rw [← unifAvg_const_mul]
  refine unifAvg_mono fun pm ↦ ?_
  have hy : |t * X pm| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hX pm) (abs_nonneg t)).trans ht
  refine (norm_cexp_mul_I_sub_le hy).trans ?_
  have h3 : |X pm| ^ 3 = |X pm| * X pm ^ 2 := by
    rw [← sq_abs (X pm)]
    ring
  rw [abs_mul, mul_pow, h3]
  calc |t| ^ 3 * (|X pm| * X pm ^ 2) ≤ |t| ^ 3 * (δ * X pm ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hX pm) (sq_nonneg _))
          (by positivity)
    _ = |t| ^ 3 * δ * X pm ^ 2 := by ring

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
    intro x y hx hxy
    have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-x) - Real.exp (-y) = Real.exp (-x) * (1 - Real.exp (-(y - x))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    have h3 : 1 - Real.exp (-(y - x)) ≤ y - x := by
      have := Real.add_one_le_exp (-(y - x))
      linarith
    have h4 : 0 ≤ 1 - Real.exp (-(y - x)) := by
      have : Real.exp (-(y - x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    have h5 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), h2]
    calc Real.exp (-x) * (1 - Real.exp (-(y - x))) ≤ 1 * (y - x) :=
          mul_le_mul h5 h3 h4 zero_le_one
      _ = -(x - y) := by ring
  rcases le_total x y with h | h
  · exact key x y hx h
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact key y x hy h

/-- The average of `e^{ix}` over real `x` has norm at most `1`. -/
theorem norm_unifAvg_cexp_le_one {α : Type*} [Fintype α] [Nonempty α] (x : α → ℝ) :
    ‖unifAvg (fun a ↦ cexp ((x a : ℂ) * I))‖ ≤ 1 := by
  refine (norm_unifAvg_le _).trans ?_
  rw [show (fun a ↦ ‖cexp ((x a : ℂ) * I)‖) = fun _ ↦ (1 : ℝ) from
    funext fun a ↦ Complex.norm_exp_ofReal_mul_I _, unifAvg_const]

/-- **Cauchy–Schwarz for an average of finite sums**:
`(E_r Σ_γ F G)² ≤ (E_r Σ_γ F²)(E_r Σ_γ G²)`. -/
theorem sq_unifAvg_sum_mul_le {R Γ : Type*} [Fintype R] [Fintype Γ] (F G : R → Γ → ℝ) :
    (unifAvg fun r ↦ ∑ γ, F r γ * G r γ) ^ 2 ≤
      (unifAvg fun r ↦ ∑ γ, F r γ ^ 2) * unifAvg fun r ↦ ∑ γ, G r γ ^ 2 := by
  unfold unifAvg
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (R × Γ))
    (fun q ↦ F q.1 q.2) (fun q ↦ G q.1 q.2)
  simp only [Fintype.sum_prod_type] at h
  have hc : (0 : ℝ) ≤ ((Fintype.card R : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((Fintype.card R : ℝ)⁻¹ * ∑ r, ∑ γ, F r γ * G r γ) ^ 2
      = ((Fintype.card R : ℝ)⁻¹) ^ 2 * (∑ r, ∑ γ, F r γ * G r γ) ^ 2 := by ring
    _ ≤ ((Fintype.card R : ℝ)⁻¹) ^ 2 * ((∑ r, ∑ γ, F r γ ^ 2) * ∑ r, ∑ γ, G r γ ^ 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

/-- **Conditional Lindeberg CLT on finite product spaces** (Lyapunov form). For each `m`, an
outer variable `r ∈ R m` (uniform) and a uniform `ρ : Γ m → P` (independent node
permutations), let `T = Σ_γ ξ m r γ (ρ γ)` with centred node terms (`E_π ξ = 0`) bounded by
`|ξ m r γ π| ≤ M m r γ`. Suppose the conditional variances `V(r) = Σ_γ E_π ξ²` satisfy
`E_r |V(r)/s_m² - 1| → 0`, that `E_r Σ_γ (M/s_m)²` stays bounded, and that
`E_r Σ_γ (M/s_m)⁴ → 0`. Then for `τ_m → t` the characteristic function `E e^{i τ_m T/s_m}`
tends to `e^{-t²/2}`. -/
theorem tendsto_unifAvg_cexp_nodeSum {R : ℕ → Type*} [∀ m, Fintype (R m)]
    [∀ m, Nonempty (R m)] {Γ : ℕ → Type*} [∀ m, Fintype (Γ m)] [∀ m, DecidableEq (Γ m)]
    {P : Type*} [Fintype P] [Nonempty P] (ξ : (m : ℕ) → R m → Γ m → P → ℝ)
    (hcent : ∀ m r γ, unifAvg (ξ m r γ) = 0) {s : ℕ → ℝ} (hs : ∀ᶠ m in atTop, 0 < s m)
    (hV : Tendsto (fun m ↦ unifAvg fun r ↦
      |(∑ γ, unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2 - 1|) atTop (𝓝 0))
    {M : (m : ℕ) → R m → Γ m → ℝ} (hM : ∀ m r γ pm, |ξ m r γ pm| ≤ M m r γ) {C : ℝ}
    (hM2 : ∀ᶠ m in atTop, (unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 2) ≤ C)
    (hM4 : Tendsto (fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 4) atTop (𝓝 0))
    {τ : ℕ → ℝ} {t : ℝ} (hτ : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun m ↦ unifAvg fun r ↦ unifAvg fun ρ : Γ m → P ↦
      cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) atTop
      (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) := by
  obtain ⟨pm₀⟩ := ‹Nonempty P›
  set Vp : (m : ℕ) → R m → ℝ := fun m r ↦ (∑ γ, unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2
    with hVp
  have hM0 : ∀ m r γ, 0 ≤ M m r γ := fun m r γ ↦ (abs_nonneg _).trans (hM m r γ pm₀)
  have hVp0 : ∀ m r, 0 ≤ Vp m r := fun m r ↦
    div_nonneg (Finset.sum_nonneg fun γ _ ↦ unifAvg_nonneg fun pm ↦ sq_nonneg _) (sq_nonneg _)
  -- the bound for one outer value `r`
  have hpt : ∀ m, 0 < s m → ∀ r,
      ‖unifAvg (fun ρ : Γ m → P ↦ cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) -
        ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
        |τ m| ^ 3 * ∑ γ, (M m r γ / s m) ^ 3 + 9 / 4 * τ m ^ 4 * ∑ γ, (M m r γ / s m) ^ 4 +
          τ m ^ 2 / 2 * |Vp m r - 1| := by
    intro m hsm r
    set x : Γ m → ℝ := fun γ ↦ |τ m| * (M m r γ / s m) with hx
    have hx0 : ∀ γ, 0 ≤ x γ := fun γ ↦ mul_nonneg (abs_nonneg _) (div_nonneg (hM0 m r γ) hsm.le)
    have h3 : ∑ γ, x γ ^ 3 = |τ m| ^ 3 * ∑ γ, (M m r γ / s m) ^ 3 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ ↦ by rw [hx]; ring
    have h4 : ∑ γ, x γ ^ 4 = τ m ^ 4 * ∑ γ, (M m r γ / s m) ^ 4 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [hx, mul_pow, show |τ m| ^ 4 = τ m ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
    have hS3 : 0 ≤ ∑ γ, x γ ^ 3 := Finset.sum_nonneg fun γ _ ↦ pow_nonneg (hx0 γ) 3
    have hS4 : 0 ≤ ∑ γ, x γ ^ 4 := Finset.sum_nonneg fun γ _ ↦ pow_nonneg (hx0 γ) 4
    have hgauss0 : 0 ≤ τ m ^ 2 / 2 * |Vp m r - 1| := by positivity
    rw [← h3, show 9 / 4 * τ m ^ 4 * ∑ γ, (M m r γ / s m) ^ 4 = 9 / 4 * ∑ γ, x γ ^ 4 by
      rw [h4]; ring]
    by_cases hgood : ∀ γ, x γ ≤ 1
    · set X : Γ m → P → ℝ := fun γ pm ↦ ξ m r γ pm / s m with hX
      have hX0 : ∀ γ, unifAvg (X γ) = 0 := fun γ ↦ by
        change unifAvg (fun pm ↦ ξ m r γ pm / s m) = 0
        rw [show (fun pm ↦ ξ m r γ pm / s m) = fun pm ↦ (s m)⁻¹ * ξ m r γ pm from
          funext fun pm ↦ by ring, unifAvg_const_mul, hcent, mul_zero]
      have hXb : ∀ γ pm, |X γ pm| ≤ M m r γ / s m := fun γ pm ↦ by
        change |ξ m r γ pm / s m| ≤ M m r γ / s m
        rw [abs_div, abs_of_pos hsm]
        exact div_le_div_of_nonneg_right (hM m r γ pm) hsm.le
      have hτδ : ∀ γ, |τ m| * (M m r γ / s m) ≤ 1 := hgood
      have hfac : unifAvg (fun ρ : Γ m → P ↦
          cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) =
          ∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) := by
        rw [← unifAvg_prod]
        congr 1
        funext ρ
        rw [← Complex.exp_sum]
        congr 1
        have e : ((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) = ∑ γ, τ m * X γ (ρ γ) := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun γ _ ↦ by rw [hX]; ring
        rw [e, Complex.ofReal_sum, Finset.sum_mul]
      set v : Γ m → ℝ := fun γ ↦ unifAvg (fun pm ↦ X γ pm ^ 2) with hv
      set a : Γ m → ℝ := fun γ ↦ τ m ^ 2 * v γ / 2 with ha
      have hvs : ∀ γ, v γ = (unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2 := fun γ ↦ by
        change unifAvg (fun pm ↦ (ξ m r γ pm / s m) ^ 2) = _
        rw [show (fun pm ↦ (ξ m r γ pm / s m) ^ 2) =
          fun pm ↦ (s m ^ 2)⁻¹ * ξ m r γ pm ^ 2 from funext fun pm ↦ by ring, unifAvg_const_mul]
        ring
      have hVsum : ∑ γ, v γ = Vp m r := by
        change ∑ γ, v γ = (∑ γ, unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun γ _ ↦ hvs γ
      have hv0 : ∀ γ, 0 ≤ v γ := fun γ ↦ unifAvg_nonneg fun pm ↦ sq_nonneg _
      have hvδ : ∀ γ, v γ ≤ (M m r γ / s m) ^ 2 := fun γ ↦ by
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hXb γ pm) 2
      have ha0 : ∀ γ, 0 ≤ a γ := fun γ ↦ by
        rw [ha]
        have := hv0 γ
        positivity
      have hax : ∀ γ, a γ ≤ x γ ^ 2 / 2 := fun γ ↦ by
        rw [ha, hx, mul_pow, sq_abs]
        have := mul_le_mul_of_nonneg_left (hvδ γ) (sq_nonneg (τ m))
        linarith
      have hx1 : ∀ γ, x γ ^ 2 ≤ 1 := fun γ ↦ by
        have := hgood γ
        have := hx0 γ
        nlinarith
      have ha1 : ∀ γ, a γ ≤ 1 := fun γ ↦ by linarith [hax γ, hx1 γ]
      have hterm : ∀ γ, ‖unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
          ((Real.exp (-a γ) : ℝ) : ℂ)‖ ≤ x γ ^ 3 + x γ ^ 4 / 4 := by
        intro γ
        have h1 := norm_unifAvg_cexp_sub_le (hX0 γ) (hXb γ) (hτδ γ)
        have h1' : |τ m| ^ 3 * (M m r γ / s m) * unifAvg (fun pm ↦ X γ pm ^ 2) ≤ x γ ^ 3 := by
          have hd0 : 0 ≤ M m r γ / s m := div_nonneg (hM0 m r γ) hsm.le
          calc |τ m| ^ 3 * (M m r γ / s m) * unifAvg (fun pm ↦ X γ pm ^ 2)
              ≤ |τ m| ^ 3 * (M m r γ / s m) * (M m r γ / s m) ^ 2 :=
                mul_le_mul_of_nonneg_left (hvδ γ) (by positivity)
            _ = x γ ^ 3 := by rw [hx]; ring
        have h2 : |Real.exp (-a γ) - 1 - (-a γ)| ≤ (-a γ) ^ 2 :=
          Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg (ha0 γ)]; exact ha1 γ)
        have h3' : ‖(((1 - τ m ^ 2 * v γ / 2 : ℝ)) : ℂ) - ((Real.exp (-a γ) : ℝ) : ℂ)‖ ≤
            x γ ^ 4 / 4 := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have heq : 1 - τ m ^ 2 * v γ / 2 - Real.exp (-a γ) =
              -(Real.exp (-a γ) - 1 - (-a γ)) := by
            rw [ha]
            ring
          rw [heq, abs_neg]
          refine h2.trans ?_
          rw [neg_sq]
          have := hax γ
          have := ha0 γ
          nlinarith
        calc ‖unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
              ((Real.exp (-a γ) : ℝ) : ℂ)‖
            ≤ ‖unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
                (((1 - τ m ^ 2 * v γ / 2 : ℝ)) : ℂ)‖ +
              ‖(((1 - τ m ^ 2 * v γ / 2 : ℝ)) : ℂ) - ((Real.exp (-a γ) : ℝ) : ℂ)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ x γ ^ 3 + x γ ^ 4 / 4 := add_le_add (h1.trans h1') h3'
      have hprod : ‖∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
          ∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ)‖ ≤ ∑ γ, x γ ^ 3 + ∑ γ, x γ ^ 4 / 4 := by
        refine (norm_prod_sub_prod_le Finset.univ _ _
          (fun γ _ ↦ norm_unifAvg_cexp_le_one _) (fun γ _ ↦ ?_)).trans ?_
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            Real.exp_le_one_iff]
          linarith [ha0 γ]
        refine (Finset.sum_le_sum fun γ _ ↦ hterm γ).trans (le_of_eq ?_)
        rw [Finset.sum_add_distrib]
      have hexp : ∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ) =
          ((Real.exp (-(τ m ^ 2 * Vp m r / 2)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
        congr 3
        simp only [ha]
        rw [← Finset.sum_div, ← Finset.mul_sum, hVsum]
      have hgauss : ‖((Real.exp (-(τ m ^ 2 * Vp m r / 2)) : ℝ) : ℂ) -
          ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ τ m ^ 2 / 2 * |Vp m r - 1| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        refine (abs_exp_neg_sub_exp_neg_le (by have := hVp0 m r; positivity)
          (by positivity)).trans (le_of_eq ?_)
        rw [show τ m ^ 2 * Vp m r / 2 - τ m ^ 2 / 2 = τ m ^ 2 / 2 * (Vp m r - 1) by ring,
          abs_mul, abs_of_nonneg (by positivity)]
      have h44 : ∑ γ, x γ ^ 4 / 4 ≤ 9 / 4 * ∑ γ, x γ ^ 4 := by
        rw [← Finset.sum_div]
        linarith
      rw [hfac]
      calc ‖∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
            ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖
          ≤ ‖∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
              ∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ)‖ +
            ‖∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ) - ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (∑ γ, x γ ^ 3 + ∑ γ, x γ ^ 4 / 4) + τ m ^ 2 / 2 * |Vp m r - 1| :=
            add_le_add hprod (by rw [hexp]; exact hgauss)
        _ ≤ _ := by linarith
    · push Not at hgood
      obtain ⟨γ₁, hγ₁⟩ := hgood
      have h1 : 1 ≤ ∑ γ, x γ ^ 4 := by
        have h1' : 1 ≤ x γ₁ ^ 4 := one_le_pow₀ hγ₁.le
        exact h1'.trans (Finset.single_le_sum (fun γ _ ↦ pow_nonneg (hx0 γ) 4)
          (Finset.mem_univ γ₁))
      have hn1 := norm_unifAvg_cexp_le_one
        (fun ρ : Γ m → P ↦ ((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ))
      have hn2 : ‖((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.exp_le_one_iff]
        have := sq_nonneg (τ m)
        linarith
      calc _ ≤ ‖unifAvg (fun ρ : Γ m → P ↦
              cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I))‖ +
            ‖((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
  -- average over `r`
  set L2 : ℕ → ℝ := fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 2 with hL2
  set L3 : ℕ → ℝ := fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 3 with hL3
  set L4 : ℕ → ℝ := fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 4 with hL4
  set Bd : ℕ → ℝ := fun m ↦ |τ m| ^ 3 * L3 m + 9 / 4 * τ m ^ 4 * L4 m +
    τ m ^ 2 / 2 * unifAvg (fun r ↦ |Vp m r - 1|) with hBd
  have havg : ∀ m, 0 < s m →
      ‖(unifAvg fun r ↦ unifAvg fun ρ : Γ m → P ↦
        cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) -
        ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ Bd m := by
    intro m hsm
    rw [← unifAvg_const_complex (α := R m) ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ),
      ← unifAvg_sub_complex]
    refine (norm_unifAvg_le _).trans ?_
    refine (unifAvg_mono fun r ↦ hpt m hsm r).trans (le_of_eq ?_)
    rw [unifAvg_add, unifAvg_add, unifAvg_const_mul, unifAvg_const_mul, unifAvg_const_mul]
  -- the third moments
  have hL3le : ∀ m, 0 < s m → L3 m ^ 2 ≤ L2 m * L4 m := by
    intro m hsm
    have h := sq_unifAvg_sum_mul_le (fun r γ ↦ M m r γ / s m) (fun r γ ↦ (M m r γ / s m) ^ 2)
    have e3 : L3 m = unifAvg fun r ↦ ∑ γ, M m r γ / s m * (M m r γ / s m) ^ 2 := by
      change (unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 3) = _
      congr 1
      funext r
      exact Finset.sum_congr rfl fun γ _ ↦ by ring
    have e4 : (unifAvg fun r ↦ ∑ γ, ((M m r γ / s m) ^ 2) ^ 2) = L4 m := by
      change _ = (unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 4)
      congr 1
      funext r
      exact Finset.sum_congr rfl fun γ _ ↦ by ring
    rw [e3, ← e4]
    exact h
  have hL0 : ∀ m, 0 < s m → 0 ≤ L3 m := fun m hsm ↦ unifAvg_nonneg fun r ↦
    Finset.sum_nonneg fun γ _ ↦ pow_nonneg (div_nonneg (hM0 m r γ) hsm.le) 3
  have hL4n : ∀ m, 0 ≤ L4 m := fun m ↦ unifAvg_nonneg fun r ↦
    Finset.sum_nonneg fun γ _ ↦ by positivity
  have hC0 : 0 ≤ C := by
    obtain ⟨m, hm⟩ := hM2.exists
    exact le_trans (unifAvg_nonneg fun r ↦ Finset.sum_nonneg fun γ _ ↦ sq_nonneg _) hm
  have hL3t : Tendsto L3 atTop (𝓝 0) := by
    have hsq : Tendsto (fun m ↦ Real.sqrt (C * L4 m)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto _).comp (hM4.const_mul C)
      rwa [mul_zero, Real.sqrt_zero] at this
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [hs] with m hsm
      exact hL0 m hsm
    · filter_upwards [hs, hM2] with m hsm hm2
      refine Real.le_sqrt_of_sq_le ((hL3le m hsm).trans ?_)
      exact mul_le_mul_of_nonneg_right hm2 (hL4n m)
  have hBd0 : Tendsto Bd atTop (𝓝 0) := by
    have h := (((hτ.abs.pow 3).mul hL3t).add (((hτ.pow 4).const_mul (9 / 4)).mul hM4)).add
      (((hτ.pow 2).div_const 2).mul hV)
    simpa only [hBd, mul_zero, add_zero] using h
  have hgl : Tendsto (fun m ↦ ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) :=
    Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ((hτ.pow 2).div_const 2).neg)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero] at hgl
  refine squeeze_zero' (Eventually.of_forall fun m ↦ norm_nonneg _) ?_ (by
    simpa only [add_zero] using hBd0.add hgl)
  filter_upwards [hs] with m hsm
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (havg m hsm) le_rfl)

end RQMCMarkov.OwenScrambling

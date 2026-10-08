/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PreludeExamples.FiniteMDP
import Mathlib.Algebra.BigOperators.Field

/-!
# Continuous-time MDPs and uniformization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.2 (pp. 28–33).

A continuous-time MDP `(Γ, δ, r, Q)` on finite `X` has a discount rate `δ > 0` and an intensity
kernel `Q` on the feasible pairs (nonnegative off the diagonal, rows summing to zero). Its
`σ`-value function is `v_σ = (δI − Q_σ)⁻¹r_σ` (1.28).

* **Uniformization** (§1.2.2.2): for `m > 0` with `|Q(x, a, x)| ≤ m` on `G`, set
  `P = I + Q/m`, `β = m/(m + δ)` and `r̂ = r/(m + δ)` (1.29)–(1.30). **Exercise 1.2.5**: `P` is
  stochastic and `v_σ = (I − βP_σ)⁻¹r̂_σ`, so the discrete-time theory applies (§1.2.2.3).
* **Exercise 1.2.6**: `v` solves the uniformized Bellman equation (1.32) iff it solves the HJB
  equation `δv(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')Q(x, a, x')}` (1.33), and the greedy
  policies of the two coincide.
* **Service rate control** (§1.2.2.4): the queue's kernel is an intensity kernel and
  `m = λ + μ̄` bounds its diagonal; the bound is attained when the capacity is at least two.
-/

open Filter Topology Set Function Matrix

namespace SargentStachurski.PreludeExamples

/-- A continuous-time MDP `(Γ, δ, r, Q)` (§1.2.2.1). -/
structure CTMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the discount rate -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- the reward rate -/
  r : X → A → ℝ
  /-- the intensity kernel -/
  Q : X → A → X → ℝ
  Q_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', x ≠ x' → 0 ≤ Q x a x'
  Q_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', Q x a x' = 0

namespace CTMDP

variable {X A : Type*} [Fintype X] [DecidableEq X] (C : CTMDP X A)

/-- `Q_σ(x, x') = Q(x, σ(x), x')`. -/
def Qσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => C.Q x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => C.r x (σ x)

/-- The `σ`-value function (1.28): `v_σ = (δI − Q_σ)⁻¹r_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ)⁻¹ *ᵥ C.rσ σ

variable {m : ℝ}

/-- The uniformized discrete-time MDP (1.29)–(1.30), for any `m > 0` bounding `|Q(x, a, x)|`
on `G`: `P = I + Q/m`, `β = m/(m + δ)`, `r̂ = r/(m + δ)`. **Exercise 1.2.5 (i)**: `P` is a
stochastic kernel. -/
noncomputable def uniformize (hm : 0 < m) (hmQ : ∀ x, ∀ a ∈ C.Γ x, |C.Q x a x| ≤ m) :
    FiniteMDP X A where
  Γ := C.Γ
  Γ_nonempty := C.Γ_nonempty
  r x a := C.r x a / (m + C.δ)
  β := m / (m + C.δ)
  β_nonneg := div_nonneg hm.le (add_pos hm C.δ_pos).le
  β_lt_one := (div_lt_one (add_pos hm C.δ_pos)).2 (lt_add_of_pos_right m C.δ_pos)
  P x a x' := (if x = x' then 1 else 0) + C.Q x a x' / m
  P_nonneg x a ha x' := by
    split_ifs with h
    · subst h
      have := (abs_le.1 (hmQ x a ha)).1
      have : -1 ≤ C.Q x a x / m := by rw [le_div_iff₀ hm]; linarith
      linarith
    · simpa using div_nonneg (C.Q_nonneg x a ha x' h) hm.le
  P_sum x a ha := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.sum_div, C.Q_sum x a ha]
    simp

variable (hm : 0 < m) (hmQ : ∀ x, ∀ a ∈ C.Γ x, |C.Q x a x| ≤ m)

/-- `δI − Q_σ = (m + δ)(I − βP_σ)`. -/
theorem sub_Qσ_eq (σ : X → A) :
    C.δ • (1 : Matrix X X ℝ) - C.Qσ σ =
      (m + C.δ) • (1 - (C.uniformize hm hmQ).β • (C.uniformize hm hmQ).Pσ σ) := by
  have hmδ : m + C.δ ≠ 0 := (add_pos hm C.δ_pos).ne'
  ext x y
  simp only [uniformize, FiniteMDP.Pσ, Qσ, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  field_simp
  split_ifs <;> ring

/-- **Exercise 1.2.5 (ii)** (p. 31): `v_σ = (δI − Q_σ)⁻¹r_σ = (I − βP_σ)⁻¹r̂_σ`, the `σ`-value
function of the uniformized MDP; in particular `δI − Q_σ` is invertible. -/
theorem vσ_eq_uniformize (σ : (C.uniformize hm hmQ).Policy) :
    IsUnit (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1) ∧
      C.vσ σ.1 = (C.uniformize hm hmQ).toDP.vσ σ := by
  obtain ⟨hU, hv⟩ := (C.uniformize hm hmQ).vσ_eq_inv σ
  have hmδ : m + C.δ ≠ 0 := (add_pos hm C.δ_pos).ne'
  have hdet := (isUnit_iff_isUnit_det _).1 hU
  have hunit2 : IsUnit (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1) := by
    rw [C.sub_Qσ_eq hm hmQ, isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hmδ)).mul hdet
  refine ⟨hunit2, ?_⟩
  have hr : (C.uniformize hm hmQ).rσ σ.1 = (m + C.δ)⁻¹ • C.rσ σ.1 := by
    funext x
    simp [uniformize, rσ, FiniteMDP.rσ, div_eq_inv_mul]
  have hB : (1 - (C.uniformize hm hmQ).β • (C.uniformize hm hmQ).Pσ σ.1) *ᵥ
      (C.uniformize hm hmQ).toDP.vσ σ = (C.uniformize hm hmQ).rσ σ.1 := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hA : (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1) *ᵥ (C.uniformize hm hmQ).toDP.vσ σ =
      C.rσ σ.1 := by
    rw [C.sub_Qσ_eq hm hmQ, smul_mulVec, hB, hr, smul_smul, mul_inv_cancel₀ hmδ, one_smul]
  rw [vσ, ← hA, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit2),
    one_mulVec]

/-- The uniformized action value is an increasing affine function of `r + ∑ vQ`. -/
theorem Q_uniformize (v : X → ℝ) (x : X) (a : A) :
    (C.uniformize hm hmQ).Q v x a =
      (C.r x a + ∑ x', v x' * C.Q x a x') / (m + C.δ) + m / (m + C.δ) * v x := by
  have hmδ : m + C.δ ≠ 0 := (add_pos hm C.δ_pos).ne'
  simp only [FiniteMDP.Q, uniformize, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hsum : ∑ x', v x' * (C.Q x a x' / m) = (∑ x', v x' * C.Q x a x') / m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsum]
  field_simp
  ring

/-- A finite maximum commutes with an increasing affine map. -/
theorem sup'_div_add {ι : Type*} (s : Finset ι) (H : s.Nonempty) (f : ι → ℝ) {d : ℝ}
    (hd : 0 < d) (e : ℝ) : s.sup' H (fun i => f i / d + e) = s.sup' H f / d + e := by
  refine le_antisymm (Finset.sup'_le _ _ fun i hi => ?_) ?_
  · exact add_le_add (div_le_div_of_nonneg_right (Finset.le_sup' f hi) hd.le) le_rfl
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' H f
    rw [heq]
    exact Finset.le_sup' (fun i => f i / d + e) hi

/-- **Exercise 1.2.6** (p. 31): `v` solves the uniformized Bellman equation (1.32) iff it solves
the HJB equation `δv(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')Q(x, a, x')}` (1.33). -/
theorem bellman_iff_hjb (v : X → ℝ) :
    (∀ x, v x = (C.Γ x).sup' (C.Γ_nonempty x) ((C.uniformize hm hmQ).Q v x)) ↔
      ∀ x, C.δ * v x = (C.Γ x).sup' (C.Γ_nonempty x)
        (fun a => C.r x a + ∑ x', v x' * C.Q x a x') := by
  have hmδ : 0 < m + C.δ := add_pos hm C.δ_pos
  refine forall_congr' fun x => ?_
  have hsup : (C.Γ x).sup' (C.Γ_nonempty x) ((C.uniformize hm hmQ).Q v x) =
      (C.Γ x).sup' (C.Γ_nonempty x) (fun a => C.r x a + ∑ x', v x' * C.Q x a x') / (m + C.δ) +
        m / (m + C.δ) * v x := by
    simp only [C.Q_uniformize hm hmQ]
    exact sup'_div_add _ _ _ hmδ _
  rw [hsup]
  set S := (C.Γ x).sup' (C.Γ_nonempty x) (fun a => C.r x a + ∑ x', v x' * C.Q x a x')
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- §1.2.2.3 (p. 31): `σ` is greedy for the uniformized MDP iff
`σ(x) ∈ argmax_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')Q(x, a, x')}` for all `x`. -/
theorem isGreedy_uniformize_iff (v : X → ℝ) (σ : (C.uniformize hm hmQ).Policy) :
    (C.uniformize hm hmQ).IsGreedy v σ ↔
      ∀ x, ∀ a ∈ C.Γ x, C.r x a + ∑ x', v x' * C.Q x a x' ≤
        C.r x (σ.1 x) + ∑ x', v x' * C.Q x (σ.1 x) x' := by
  have hmδ : 0 < m + C.δ := add_pos hm C.δ_pos
  refine forall_congr' fun x => forall₂_congr fun a _ => ?_
  rw [C.Q_uniformize hm hmQ, C.Q_uniformize hm hmQ, add_le_add_iff_right,
    div_le_div_iff_of_pos_right hmδ]

end CTMDP

/-! ### Service rate control -/

/-- The off-diagonal rates of the queue in §1.2.2.4: arrivals at rate `λ` (`x → x + 1`) and
service at rate `μ(a)` (`x → x − 1`). -/
def queueRate {N : ℕ} {A : Type*} (lam : ℝ) (μ : A → ℝ) (x : Fin (N + 1)) (a : A)
    (y : Fin (N + 1)) : ℝ :=
  (if (y : ℕ) = x + 1 then lam else 0) + (if (y : ℕ) + 1 = x then μ a else 0)

/-- The queue's intensity kernel: the rates off the diagonal, minus their sum on it. -/
def queueQ {N : ℕ} {A : Type*} (lam : ℝ) (μ : A → ℝ) (x : Fin (N + 1)) (a : A)
    (y : Fin (N + 1)) : ℝ :=
  if y = x then -∑ z, queueRate lam μ x a z else queueRate lam μ x a y

theorem sum_fin_ite_val_eq {N : ℕ} (k : ℕ) (c : ℝ) :
    ∑ z : Fin (N + 1), (if (z : ℕ) = k then c else 0) = if k < N + 1 then c else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = k then c else 0), Finset.sum_ite_eq']
  simp

/-- The diagonal of the queue's kernel: `Q(x, a, x) = −(λ𝟙{x < N} + μ(a)𝟙{x > 0})`. -/
theorem queueQ_diag {N : ℕ} {A : Type*} (lam : ℝ) (μ : A → ℝ) (x : Fin (N + 1)) (a : A) :
    queueQ lam μ x a x =
      -((if (x : ℕ) < N then lam else 0) + (if 0 < (x : ℕ) then μ a else 0)) := by
  simp only [queueQ, ↓reduceIte, queueRate, Finset.sum_add_distrib, sum_fin_ite_val_eq]
  congr 1
  have hx := x.isLt
  congr 1
  · by_cases h : (x : ℕ) < N
    · have h' : (x : ℕ) + 1 < N + 1 := by omega
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ (x : ℕ) + 1 < N + 1 := by omega
      simp only [h, h', ↓reduceIte]
  · rcases Nat.eq_zero_or_pos (x : ℕ) with h0 | hpos
    · have h' : ¬ 0 < (x : ℕ) := by omega
      simp only [h', ↓reduceIte]
      refine Finset.sum_eq_zero fun z _ => ?_
      have hz : ¬ ((z : ℕ) + 1 = x) := by omega
      simp only [hz, ↓reduceIte]
    · obtain ⟨j, hj⟩ : ∃ j, (x : ℕ) = j + 1 := ⟨(x : ℕ) - 1, by omega⟩
      have : ∀ z : Fin (N + 1), ((z : ℕ) + 1 = x) ↔ ((z : ℕ) = j) := fun z => by omega
      have hj' : j < N + 1 := by omega
      simp only [hpos, this, sum_fin_ite_val_eq, hj', ↓reduceIte]

/-- §1.2.2.4: the service rate control problem as a continuous-time MDP: `Q` is an intensity
kernel, all actions are feasible, and `r(x, a) = μ(a)R𝟙{x > 0} − hx − c(a)`. -/
def serviceRate (N : ℕ) {A : Type*} (Γ : Finset A) (hΓ : Γ.Nonempty) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (R h δ : ℝ) (hδ : 0 < δ) (c : A → ℝ) :
    CTMDP (Fin (N + 1)) A where
  Γ _ := Γ
  Γ_nonempty _ := hΓ
  δ := δ
  δ_pos := hδ
  r x a := μ a * R * (if 0 < (x : ℕ) then 1 else 0) - h * x - c a
  Q := queueQ lam μ
  Q_nonneg x a _ y hxy := by
    simp only [queueQ, Ne.symm hxy, ↓reduceIte, queueRate]
    exact add_nonneg (by split_ifs <;> simp [hlam]) (by split_ifs <;> simp [hμ a])
  Q_sum x a _ := by
    have hxx : queueRate lam μ x a x = 0 := by simp [queueRate]
    have h1 := Finset.add_sum_erase Finset.univ (queueQ lam μ x a) (Finset.mem_univ x)
    have h2 := Finset.add_sum_erase Finset.univ (queueRate lam μ x a) (Finset.mem_univ x)
    have h3 : ∑ y ∈ Finset.univ.erase x, queueQ lam μ x a y =
        ∑ y ∈ Finset.univ.erase x, queueRate lam μ x a y :=
      Finset.sum_congr rfl fun y hy => by simp only [queueQ, Finset.ne_of_mem_erase hy, ↓reduceIte]
    have h4 : queueQ lam μ x a x = -∑ z, queueRate lam μ x a z := by simp [queueQ]
    rw [← h1, h3, h4, ← h2, hxx]
    ring

/-- §1.2.2.4 (p. 32): `m = λ + μ̄` bounds the diagonal, `|Q(x, a, x)| ≤ λ + μ̄` where
`μ̄ ≥ μ(a)` for all `a`. -/
theorem abs_queueQ_diag_le {N : ℕ} {A : Type*} {lam : ℝ} (hlam : 0 ≤ lam) {μ : A → ℝ}
    (hμ : ∀ a, 0 ≤ μ a) {μbar : ℝ} (hμbar : ∀ a, μ a ≤ μbar) (x : Fin (N + 1)) (a : A) :
    |queueQ lam μ x a x| ≤ lam + μbar := by
  rw [queueQ_diag, abs_neg, abs_of_nonneg (add_nonneg (by split_ifs <;> simp [hlam])
    (by split_ifs <;> simp [hμ a]))]
  refine add_le_add (by split_ifs <;> simp [hlam]) ?_
  split_ifs
  · exact hμbar a
  · exact (hμ a).trans (hμbar a)

/-- §1.2.2.4 (p. 32): when the capacity is `N ≥ 2`, an interior state `0 < x < N` exists and
`|Q(x, a, x)| = λ + μ(a)` there, so `m = λ + μ̄` is the maximum of `|Q(x, a, x)|`. -/
theorem abs_queueQ_diag_interior {N : ℕ} (hN : 2 ≤ N) {A : Type*} {lam : ℝ} (hlam : 0 ≤ lam)
    {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (a : A) :
    |queueQ lam μ (⟨1, by omega⟩ : Fin (N + 1)) a ⟨1, by omega⟩| = lam + μ a := by
  rw [queueQ_diag]
  simp only [show (1 : ℕ) < N by omega, ↓reduceIte, zero_lt_one, abs_neg]
  exact abs_of_nonneg (add_nonneg hlam (hμ a))

/-- §1.2.2.4: with capacity `N = 1` there is no interior state, and the largest `|Q(x, a, x)|`
is `max(λ, μ̄)`, not `λ + μ̄`; `λ + μ̄` is still a valid uniformization rate. -/
theorem abs_queueQ_diag_capacity_one {A : Type*} {lam : ℝ} (hlam : 0 ≤ lam) {μ : A → ℝ}
    (hμ : ∀ a, 0 ≤ μ a) (x : Fin 2) (a : A) :
    |queueQ lam μ x a x| = if (x : ℕ) = 0 then lam else μ a := by
  rw [queueQ_diag]
  fin_cases x
  · simp [abs_of_nonneg hlam]
  · simp [abs_of_nonneg (hμ a)]

/-- §1.2.2.4: the service rate problem uniformized at `m = λ + μ̄` (`λ > 0`). -/
noncomputable def serviceRateMDP (N : ℕ) {A : Type*} (Γ : Finset A) (hΓ : Γ.Nonempty) {lam : ℝ}
    (hlam : 0 < lam) {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) {μbar : ℝ} (hμbar : ∀ a, μ a ≤ μbar)
    (R h δ : ℝ) (hδ : 0 < δ) (c : A → ℝ) : FiniteMDP (Fin (N + 1)) A :=
  (serviceRate N Γ hΓ lam hlam.le μ hμ R h δ hδ c).uniformize
    (m := lam + μbar) (add_pos_of_pos_of_nonneg hlam ((hμ hΓ.choose).trans (hμbar _)))
    fun x a _ => abs_queueQ_diag_le hlam.le hμ hμbar x a

/-- §1.2.2.4 (p. 32): for the service rate problem the value function solves the HJB equation
(1.33) and an optimal policy exists, which HPI finds in finitely many steps. -/
theorem serviceRate_optimality (N : ℕ) {A : Type*} (Γ : Finset A) (hΓ : Γ.Nonempty) {lam : ℝ}
    (hlam : 0 < lam) {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) {μbar : ℝ} (hμbar : ∀ a, μ a ≤ μbar)
    (R h δ : ℝ) (hδ : 0 < δ) (c : A → ℝ) :
    (∀ x, δ * (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.vstar x =
      Γ.sup' hΓ (fun a => (μ a * R * (if 0 < (x : ℕ) then 1 else 0) - h * x - c a) +
        ∑ x', (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.vstar x' *
          queueQ lam μ x a x')) ∧
      (∃ σ, (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.IsOptimal σ) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.IsOptimal
        ((serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).toDP.hpiPolicy σ₀ j) := by
  obtain ⟨-, hbell, -, -, hex⟩ := (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).theorem_1_2_1
  obtain ⟨-, -, hhpi⟩ := (serviceRateMDP N Γ hΓ hlam hμ hμbar R h δ hδ c).theorem_1_2_2
  refine ⟨(CTMDP.bellman_iff_hjb _ _ _ _).1 hbell, hex, fun σ₀ => ?_⟩
  obtain ⟨k, hk⟩ := hhpi σ₀
  exact ⟨k, fun j hj => (hk j hj).2⟩

end SargentStachurski.PreludeExamples

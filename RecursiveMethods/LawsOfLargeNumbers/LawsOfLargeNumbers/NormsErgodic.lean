/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Minimum norm duality and the Norms Ergodic Lemma

SLP §14.2, pp. 430–435. `X` is a real normed space and `X*` (`StrongDual ℝ X`) its dual.

* **Theorem 14.10** (`theorem_14_10`, minimum norm duality, p. 432): for a subspace `M`,
  `inf_{y ∈ M} ‖x − y‖ = max {⟨x, μ⟩ : ‖μ‖ ≤ 1, μ = 0 on M}`, and the maximum is attained. The
  book cites Luenberger. Here the maximiser is a norm-one functional on the quotient `X/M`, from
  Hahn–Banach, composed with the quotient map; `‖x + M‖ = inf_{y ∈ M} ‖x − y‖`.
* **Lemma 14.11** (`lemma_14_11`, p. 432): a weak limit of a sequence in a subspace lies in its
  norm closure (`mem_closure_of_weak`); in the book the subspace is the image `TX`.
* **Exercise 14.3** (`ex_14_3a`, `ex_14_3b`, pp. 432–433): `Tᵏ` and
  `Hₙ = (1/n) Σ_{k=1}^n T^{k−1}` (`cesaroOp`) are linear, with norms `≤ 1` when `‖T‖ ≤ 1`.
* **Lemma 14.12** (`lemma_14_12`, p. 433): `‖Hₙx‖ → 0` for `x` in the closure of `(T − I)X`.
* **Lemma 14.13** (`lemma_14_13`, the Norms Ergodic Lemma, p. 434): if `Tx̄ = x̄` and `Hₙx → x̄`
  weakly then `Hₙx → x̄` in norm.

**Corrections.**
* The book's space `L` of linear operators (p. 431) includes unbounded operators, for which
  `‖T‖_L = ∞`. Operators here are continuous (`X →L[ℝ] X`); every operator used later has
  `‖T‖ ≤ 1`.
* Lemmas 14.12 and 14.13 assume `‖T‖ = 1`; only `‖T‖ ≤ 1` is used.
* In the proof of Lemma 14.13 the weak limit of `(Hₙ − I)x` is `x̄ − x`; the book writes
  `x − x̄` (harmless: the closed subspace is symmetric).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open Filter Topology Metric

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Theorem 14.10 -/

/-- The quotient norm is the distance to the subspace. -/
theorem norm_quotient_mk (M : Submodule ℝ X) (x : X) :
    ‖(Submodule.Quotient.mk x : X ⧸ M)‖ = infDist x (M : Set X) :=
  QuotientAddGroup.norm_mk (S := M.toAddSubgroup) x

/-- **Theorem 14.10** (minimum norm duality). For a subspace `M` and `x ∈ X`, every `μ ∈ X*` with
`‖μ‖ ≤ 1` vanishing on `M` has `⟨x, μ⟩ ≤ inf_{y ∈ M} ‖x − y‖`, and some such `μ*` attains it. -/
theorem theorem_14_10 (M : Submodule ℝ X) (x : X) :
    IsGreatest {r | ∃ μ : StrongDual ℝ X, ‖μ‖ ≤ 1 ∧ (∀ y ∈ M, μ y = 0) ∧ r = μ x}
      (infDist x (M : Set X)) := by
  constructor
  · obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (Submodule.Quotient.mk x : X ⧸ M)
    have hb : ∀ y : X, ‖(g.toLinearMap.comp M.mkQ) y‖ ≤ 1 * ‖y‖ := fun y => by
      change ‖g (Submodule.Quotient.mk y)‖ ≤ 1 * ‖y‖
      calc ‖g (Submodule.Quotient.mk y)‖ ≤ ‖g‖ * ‖(Submodule.Quotient.mk y : X ⧸ M)‖ :=
            g.le_opNorm _
        _ ≤ 1 * ‖y‖ := mul_le_mul hg1 (Submodule.Quotient.norm_mk_le M y) (norm_nonneg _)
            zero_le_one
    refine ⟨(g.toLinearMap.comp M.mkQ).mkContinuous 1 hb,
      LinearMap.mkContinuous_norm_le _ zero_le_one hb, fun y hy => ?_, ?_⟩
    · change g (Submodule.Quotient.mk y) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).2 hy, map_zero]
    · change _ = g (Submodule.Quotient.mk x)
      rw [hgx, norm_quotient_mk]
      rfl
  · rintro r ⟨μ, hμ1, hμM, rfl⟩
    rw [infDist_eq_iInf]
    have : Nonempty (M : Set X) := ⟨⟨0, M.zero_mem⟩⟩
    refine le_ciInf fun y => ?_
    have h0 : μ x = μ (x - y) := by rw [map_sub, hμM y y.2, sub_zero]
    rw [h0, dist_eq_norm]
    exact (le_abs_self _).trans ((μ.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hμ1))

/-! ### Lemma 14.11 -/

/-- A weak limit of a sequence in a subspace `M` lies in the norm closure of `M`. -/
theorem mem_closure_of_weak (M : Submodule ℝ X) {x : X} {xs : ℕ → X} (hxs : ∀ n, xs n ∈ M)
    (hw : ∀ μ : StrongDual ℝ X, Tendsto (fun n => μ (xs n)) atTop (𝓝 (μ x))) :
    x ∈ closure (M : Set X) := by
  obtain ⟨⟨μ, -, hμM, hμx⟩, -⟩ := theorem_14_10 M x
  have hlim := hw μ
  simp only [hμM _ (hxs _)] at hlim
  rw [mem_closure_iff_infDist_zero ⟨0, M.zero_mem⟩, hμx]
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Lemma 14.11.** If `T` is linear, `xₙ ∈ TX` and `⟨xₙ, μ⟩ → ⟨x, μ⟩` for all `μ ∈ X*`, then
`x` lies in the closure of `TX`. -/
theorem lemma_14_11 (T : X →ₗ[ℝ] X) {x : X} {xs : ℕ → X} (hxs : ∀ n, xs n ∈ LinearMap.range T)
    (hw : ∀ μ : StrongDual ℝ X, Tendsto (fun n => μ (xs n)) atTop (𝓝 (μ x))) :
    x ∈ closure (LinearMap.range T : Set X) :=
  mem_closure_of_weak _ hxs hw

/-! ### Exercise 14.3 -/

/-- **Exercise 14.3a.** `T⁰ = I`, `Tᵏx = T(T^{k−1}x)`, each `Tᵏ` is linear, and `‖Tᵏ‖ ≤ 1` when
`‖T‖ ≤ 1`. -/
theorem ex_14_3a (T : X →L[ℝ] X) :
    T ^ 0 = ContinuousLinearMap.id ℝ X ∧ (∀ k x, (T ^ (k + 1)) x = T ((T ^ k) x)) ∧
      (∀ k (a b : ℝ) (x y : X), (T ^ k) (a • x + b • y) = a • (T ^ k) x + b • (T ^ k) y) ∧
      (‖T‖ ≤ 1 → ∀ k, ‖T ^ k‖ ≤ 1) := by
  refine ⟨pow_zero T, fun k x => by rw [pow_succ']; rfl,
    fun k a b x y => by rw [map_add, map_smul, map_smul], fun hT k => ?_⟩
  induction k with
  | zero =>
    rw [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ']
    calc ‖T * T ^ k‖ ≤ ‖T‖ * ‖T ^ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hT ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The Cesàro operator `Hₙ = (1/n) Σ_{k=1}^n T^{k−1}` ((8), p. 433). -/
noncomputable def cesaroOp (T : X →L[ℝ] X) (n : ℕ) : X →L[ℝ] X :=
  (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, T ^ k

theorem cesaroOp_apply (T : X →L[ℝ] X) (n : ℕ) (x : X) :
    cesaroOp T n x = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, (T ^ k) x := by
  simp [cesaroOp]

/-- **Exercise 14.3b.** Each `Hₙ` is linear, and `‖Hₙ‖ ≤ 1` when `‖T‖ ≤ 1`. -/
theorem ex_14_3b (T : X →L[ℝ] X) :
    (∀ n (a b : ℝ) (x y : X),
      cesaroOp T n (a • x + b • y) = a • cesaroOp T n x + b • cesaroOp T n y) ∧
      (‖T‖ ≤ 1 → ∀ n, ‖cesaroOp T n‖ ≤ 1) := by
  refine ⟨fun n a b x y => by rw [map_add, map_smul, map_smul], fun hT n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cesaroOp]
  · have hsum : ‖∑ k ∈ Finset.range n, T ^ k‖ ≤ n := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => (ex_14_3a T).2.2.2 hT k
      simpa using this
    rw [cesaroOp, norm_smul, norm_inv, Real.norm_natCast]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [inv_mul_le_iff₀ hn', mul_one]
    exact hsum

/-! ### Lemmas 14.12 and 14.13 -/

/-- `Hₙ(T − I)y = (Tⁿy − y)/n`. -/
theorem cesaroOp_sub_one (T : X →L[ℝ] X) (n : ℕ) (y : X) :
    cesaroOp T n ((T - 1) y) = (n : ℝ)⁻¹ • ((T ^ n) y - y) := by
  rw [cesaroOp_apply]
  congr 1
  have : ∀ k, (T ^ k) ((T - 1) y) = (T ^ (k + 1)) y - (T ^ k) y := fun k => by
    rw [pow_succ]
    change (T ^ k) (T y - y) = (T ^ k) (T y) - (T ^ k) y
    rw [map_sub]
  simp_rw [this]
  rw [Finset.sum_range_sub (fun k => (T ^ k) y), pow_zero]
  rfl

/-- **Lemma 14.12.** If `‖T‖ ≤ 1`, then `‖Hₙx‖ → 0` for every `x` in the closure of `(T − I)X`. -/
theorem lemma_14_12 (T : X →L[ℝ] X) (hT : ‖T‖ ≤ 1) {x : X}
    (hx : x ∈ closure (LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X) : Set X)) :
    Tendsto (fun n => ‖cesaroOp T n x‖) atTop (𝓝 0) := by
  -- Step 1: on `(T − I)X`
  have hstep : ∀ y : X, Tendsto (fun n => ‖cesaroOp T n ((T - 1) y)‖) atTop (𝓝 0) := fun y => by
    have hb : ∀ n : ℕ, ‖cesaroOp T n ((T - 1) y)‖ ≤ 2 * ‖y‖ * (n : ℝ)⁻¹ := fun n => by
      rw [cesaroOp_sub_one, norm_smul, norm_inv, Real.norm_natCast]
      have h1 : ‖(T ^ n) y - y‖ ≤ 2 * ‖y‖ := by
        refine (norm_sub_le _ _).trans ?_
        have := ((T ^ n).le_opNorm y).trans
          (mul_le_of_le_one_left (norm_nonneg _) ((ex_14_3a T).2.2.2 hT n))
        linarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Nat.cast_nonneg n))
    have hlim : Tendsto (fun n : ℕ => 2 * ‖y‖ * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 * ‖y‖)
    exact squeeze_zero (fun n => norm_nonneg _) hb hlim
  -- Step 2: approximation
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨x', hx'⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  obtain ⟨⟨y, rfl⟩, hd⟩ := hx'
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hstep y) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1 ⊢
  have h2 : ‖cesaroOp T n (x - (T - 1) y)‖ ≤ ‖x - (T - 1) y‖ :=
    ((cesaroOp T n).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((ex_14_3b T).2 hT n))
  have h3 : ‖x - (T - 1) y‖ < ε / 2 := by rwa [← dist_eq_norm]
  have h4 : cesaroOp T n x = cesaroOp T n ((T - 1) y) + cesaroOp T n (x - (T - 1) y) := by
    rw [← map_add, add_sub_cancel]
  rw [h4]
  linarith [norm_add_le (cesaroOp T n ((T - 1) y)) (cesaroOp T n (x - (T - 1) y))]

/-- `Hₙx − x ∈ (T − I)X`. -/
theorem cesaroOp_sub_mem_range (T : X →L[ℝ] X) (n : ℕ) (hn : 1 ≤ n) (x : X) :
    cesaroOp T n x - x ∈ LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X) := by
  set R := LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X)
  have hk : ∀ k, (T ^ k) x - x ∈ R := fun k => by
    induction k with
    | zero => simp [R]
    | succ k ih =>
      have : (T ^ (k + 1)) x - x = (T - 1) ((T ^ k) x) + ((T ^ k) x - x) := by
        rw [pow_succ']
        change T ((T ^ k) x) - x = (T ((T ^ k) x) - (T ^ k) x) + ((T ^ k) x - x)
        abel
      rw [this]
      exact R.add_mem ⟨_, rfl⟩ ih
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : cesaroOp T n x - x = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, ((T ^ k) x - x) := by
    rw [cesaroOp_apply, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [this]
  exact R.smul_mem _ (R.sum_mem fun k _ => hk k)

/-- `Hₙx̄ = x̄` for a fixed point `x̄` of `T` and `n ≥ 1`. -/
theorem cesaroOp_fixed (T : X →L[ℝ] X) {xbar : X} (hfix : T xbar = xbar) {n : ℕ} (hn : 1 ≤ n) :
    cesaroOp T n xbar = xbar := by
  have hk : ∀ k, (T ^ k) xbar = xbar := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      change T ((T ^ k) xbar) = xbar
      rw [ih, hfix]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [cesaroOp_apply]
  simp_rw [hk]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hn', one_smul]

/-- **Lemma 14.13** (Norms Ergodic Lemma). Let `‖T‖ ≤ 1` and `Tx̄ = x̄`. If `⟨Hₙx, μ⟩ → ⟨x̄, μ⟩`
for every `μ ∈ X*`, then `‖Hₙx − x̄‖ → 0`. -/
theorem lemma_14_13 (T : X →L[ℝ] X) (hT : ‖T‖ ≤ 1) {xbar x : X} (hfix : T xbar = xbar)
    (hw : ∀ μ : StrongDual ℝ X, Tendsto (fun n => μ (cesaroOp T n x)) atTop (𝓝 (μ xbar))) :
    Tendsto (fun n => ‖cesaroOp T n x - xbar‖) atTop (𝓝 0) := by
  set R := LinearMap.range ((T - 1 : X →L[ℝ] X) : X →ₗ[ℝ] X)
  -- `yₙ = H_{n+1}x − x ∈ (T − I)X` converges weakly to `x̄ − x`
  have hmem : xbar - x ∈ closure (R : Set X) := by
    refine mem_closure_of_weak R (xs := fun n => cesaroOp T (n + 1) x - x)
      (fun n => cesaroOp_sub_mem_range T (n + 1) (by omega) x) fun μ => ?_
    simp only [map_sub]
    exact ((hw μ).comp (tendsto_add_atTop_nat 1)).sub tendsto_const_nhds
  have hc : (R.topologicalClosure : Set X) = closure (R : Set X) :=
    Submodule.topologicalClosure_coe R
  have hmem' : x - xbar ∈ closure (R : Set X) := by
    rw [← hc] at hmem ⊢
    have := R.topologicalClosure.neg_mem hmem
    rwa [neg_sub] at this
  have hlim := lemma_14_12 T hT hmem'
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  rw [map_sub, cesaroOp_fixed T hfix hn]

end StokeyLucasPrescott.LawsOfLargeNumbers

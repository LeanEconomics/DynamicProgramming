/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.EulerEquations
import DeterministicDP.Assumption42

/-!
# Optimal policies from the Euler equations

SLP Exercise 4.9, pp. 99–100.

* `ex_4_9a`: in the unit-elastic growth model `F(k, y) = ln(k^α − y)` on `k > 0`, the plan
  `k_{t+1} = αβk_t^α` satisfies the Euler equations and the transversality condition, so it is
  optimal by Theorem 4.15.
* `ex_4_9b`: in the quadratic investment model `F(x, y) = ax − bx²/2 − c(y − x)²/2` on `ℝ`, the
  linear policy `g(x) = (δα + cx)/(δβ + c)` satisfies the Euler equations and is optimal.
  Theorem 4.15 itself does not apply, since the state space is `ℝ` and `F_x` takes both signs.
  The sufficiency argument goes through with `euler_sufficient`: a plan with `u(x) > −∞` has
  `Σ δᵗx_t² < ∞`, so `δᵗx_t → 0` and the boundary terms vanish.
-/

open Filter Topology Real

namespace StokeyLucasPrescott.DeterministicDP

/-! ### Exercise 4.9a: the unit-elastic growth model -/

variable {α β : ℝ}

/-- `Γ(k) = {y : 0 < y < k^α}` for `k > 0` (empty otherwise). -/
def egΓ (α : ℝ) (k : ℝ) : Set ℝ := {y | 0 < k ∧ 0 < y ∧ y < k ^ α}

/-- `F(k, y) = ln(k^α − y)`. -/
noncomputable def egF (α : ℝ) (p : ℝ × ℝ) : ℝ := Real.log (p.1 ^ α - p.2)

/-- The derivative of `F` at `(k, y)`. -/
noncomputable def egD (α k y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (k ^ α - y)⁻¹ • ((α * k ^ (α - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem egF_hasFDerivAt {k y : ℝ} (hk : 0 < k) (hy : y < k ^ α) :
    HasFDerivAt (egF α) (egD α k y) (k, y) := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (k, y))).rpow_const
    (p := α) (Or.inl hk.ne')
  have h2 := (h1.sub (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (k, y)))).log
    (by simp; linarith)
  exact h2

theorem egFx (k y v : ℝ) : Fx (egD α k y) v = (k ^ α - y)⁻¹ * (α * k ^ (α - 1) * v) := by
  simp [Fx, egD]

theorem egFy (k y w : ℝ) : Fy (egD α k y) w = -((k ^ α - y)⁻¹ * w) := by
  simp [Fy, egD]

/-- The graph `{(k, y) : k > 0, 0 < y < k^α}` is convex and `F` is concave on it. -/
theorem egF_concave (hα0 : 0 < α) (hα1 : α < 1) :
    ConcaveOn ℝ {p : ℝ × ℝ | p.2 ∈ egΓ α p.1} (egF α) := by
  have hrp := Real.concaveOn_rpow hα0.le hα1.le
  have hconv : Convex ℝ {p : ℝ × ℝ | p.2 ∈ egΓ α p.1} := by
    rintro ⟨k, y⟩ ⟨hk, hy0, hy⟩ ⟨k', y'⟩ ⟨hk', hy0', hy'⟩ a b ha hb hab
    have hc := hrp.2 (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 hk'.le) ha hb hab
    simp only [smul_eq_mul] at hc
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simp [hk']
      · nlinarith
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simp [hy0']
      · nlinarith
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simp [hy']
      · nlinarith
  refine ⟨hconv, ?_⟩
  rintro ⟨k, y⟩ ⟨hk, hy0, hy⟩ ⟨k', y'⟩ ⟨hk', hy0', hy'⟩ a b ha hb hab
  have hc := hrp.2 (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 hk'.le) ha hb hab
  simp only [smul_eq_mul] at hc
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (by linarith : 0 < k ^ α - y))
    (Set.mem_Ioi.2 (by linarith : 0 < k' ^ α - y')) ha hb hab
  simp only [smul_eq_mul] at hlog
  simp only [egF, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine hlog.trans (Real.log_le_log ?_ (by linarith))
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp; linarith
  · nlinarith

/-- Feasible plans are positive. -/
theorem eg_pos {x₀ : ℝ} {x : ℕ → ℝ} (hx : x ∈ Feasible (egΓ α) x₀) (t : ℕ) : 0 < x t :=
  (hx.2 t).1

theorem eg_assumption42 (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Assumption42 (egΓ α) (fun x y => egF α (x, y)) β := by
  refine assumption42_of_summable_pos fun x₀ x hx => ?_
  have hx0 : 0 < x₀ := hx.1 ▸ eg_pos hx 0
  have hlog : ∀ t, Real.log (x t) ≤ α ^ t * Real.log x₀ := by
    intro t
    induction t with
    | zero => simp [hx.1]
    | succ t ih =>
      have h := Real.log_lt_log (hx.2 t).2.1 (hx.2 t).2.2
      rw [Real.log_rpow (eg_pos hx t)] at h
      calc Real.log (x (t + 1)) ≤ α * Real.log (x t) := h.le
        _ ≤ α * (α ^ t * Real.log x₀) := mul_le_mul_of_nonneg_left ih hα0.le
        _ = α ^ (t + 1) * Real.log x₀ := by ring
  have hαβ : α * β < 1 := by nlinarith
  refine summable_max_of_le_geometric (mul_pos hα0 hβ0).le hαβ
    (by positivity : (0 : ℝ) ≤ α * |Real.log x₀|) fun t => ?_
  have hpos : 0 < x t ^ α - x (t + 1) := by linarith [(hx.2 t).2.2]
  have hF : egF α (x t, x (t + 1)) ≤ α * Real.log (x t) := by
    simp only [egF]
    rw [← Real.log_rpow (eg_pos hx t)]
    exact Real.log_le_log hpos (by linarith [(hx.2 t).2.1])
  calc β ^ t * egF α (x t, x (t + 1)) ≤ β ^ t * (α * (α ^ t * |Real.log x₀|)) := by
        refine mul_le_mul_of_nonneg_left (hF.trans (mul_le_mul_of_nonneg_left ((hlog t).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hα0.le t))) hα0.le))
          (pow_nonneg hβ0.le t)
    _ = α * |Real.log x₀| * (α * β) ^ t := by rw [mul_pow]; ring

/-- **Exercise 4.9a.** The plan `k_{t+1} = αβk_t^α` from `k₀ > 0` is optimal (Theorem 4.15). -/
theorem ex_4_9a (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) {k₀ : ℝ}
    (hk₀ : 0 < k₀) :
    total (fun x y => egF α (x, y)) β (fun t => (fun k => α * β * k ^ α)^[t] k₀) =
      vstar (egΓ α) (fun x y => egF α (x, y)) β k₀ := by
  have hαβ : α * β < 1 := by nlinarith
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set k : ℕ → ℝ := fun t => (fun k => α * β * k ^ α)^[t] k₀
  have hk : ∀ t, k (t + 1) = α * β * k t ^ α := fun t => Function.iterate_succ_apply' _ _ _
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk₀
    | succ t ih => rw [hk]; have := rpow_pos_of_pos ih α; positivity
  have hlt : ∀ t, k (t + 1) < k t ^ α := fun t => by
    rw [hk]; have := rpow_pos_of_pos (hkpos t) α; nlinarith
  have hfeas : k ∈ Feasible (egΓ α) k₀ := ⟨rfl, fun t => ⟨hkpos t, hkpos (t + 1), hlt t⟩⟩
  -- consumption `c_t = (1 − αβ)k_t^α`
  have hc : ∀ t, k t ^ α - k (t + 1) = (1 - α * β) * k t ^ α := fun t => by rw [hk]; ring
  refine theorem_4_15 (eg_assumption42 hα0 hα1 hβ0 hβ1) hβ0.le (egF_concave hα0 hα1)
    (fun x₀ x hx t => (eg_pos hx t).le) hfeas (fun t => egD α (k t) (k (t + 1)))
    (fun t => egF_hasFDerivAt (hkpos t) (hlt t)) (fun t v hv => ?_) (fun t v => ?_) ?_
  · rw [egFx]
    have := rpow_pos_of_pos (hkpos t) (α - 1)
    have hpos : 0 < k t ^ α - k (t + 1) := by linarith [hlt t]
    positivity
  · -- the Euler equation
    rw [egFy, egFx, hc, hc]
    have hK := rpow_pos_of_pos (hkpos t) α
    have hK' := rpow_pos_of_pos (hkpos (t + 1)) α
    rw [Real.rpow_sub_one (hkpos (t + 1)).ne', hk t]
    have hne : 1 - α * β ≠ 0 := by linarith
    field_simp
    ring
  · -- transversality: `βᵗF_x·k_t = βᵗα/(1 − αβ)`
    have e : ∀ t, β ^ t * Fx (egD α (k t) (k (t + 1))) (k t) = α / (1 - α * β) * β ^ t := by
      intro t
      rw [egFx, hc, Real.rpow_sub_one (hkpos t).ne']
      have hK := rpow_pos_of_pos (hkpos t) α
      have hne : 1 - α * β ≠ 0 := by linarith
      have := (hkpos t).ne'
      field_simp
    simp only [e]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (α / (1 - α * β))

/-! ### Exercise 4.9b: the quadratic investment model -/

variable {a b c δ : ℝ}

/-- `F(x, y) = ax − bx²/2 − c(y − x)²/2`. -/
noncomputable def qF (a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  a * p.1 - b * p.1 ^ 2 / 2 - c * (p.2 - p.1) ^ 2 / 2

/-- Its derivative at `(x, y)`: `F_x = a − bx + c(y − x)`, `F_y = −c(y − x)`. -/
noncomputable def qD (a b c x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (a - b * x + c * (y - x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (-(c * (y - x))) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem qFx (x y v : ℝ) : Fx (qD a b c x y) v = (a - b * x + c * (y - x)) * v := by
  simp [Fx, qD]

theorem qFy (x y w : ℝ) : Fy (qD a b c x y) w = -(c * (y - x)) * w := by
  simp [Fy, qD]

/-- `F` lies below its tangent planes: the gap is `−b(x − x*)²/2 − c((y − x) − (y* − x*))²/2`. -/
theorem qF_le (hb : 0 < b) (hc : 0 < c) (x y x' y' : ℝ) :
    qF a b c (x, y) ≤ qF a b c (x', y') + qD a b c x' y' ((x, y) - (x', y')) := by
  simp only [qF, qD, Prod.mk_sub_mk, FunLike.coe_add, FunLike.coe_smul,
    Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  nlinarith [sq_nonneg (x - x'), sq_nonneg ((y - x) - (y' - x'))]

/-- **Exercise 4.9b.** If `β` and `α` solve (6)–(7) in the limit,
`β = b + δβc/(δβ + c)` and `α = a + δαc/(δβ + c)` with `β > 0`, then the linear policy
`g(x) = (δα + cx)/(δβ + c)` satisfies the Euler equations and generates optimal plans. -/
theorem ex_4_9b (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {P Q : ℝ} (hQ0 : 0 < Q) (hQ : b + δ * Q * c / (δ * Q + c) = Q)
    (hP : a + δ * P * c / (δ * Q + c) = P) {x₀ : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = x₀)
    (hx : ∀ t, x (t + 1) = (δ * P + c * x t) / (δ * Q + c)) :
    total (fun x y => qF a b c (x, y)) δ x =
      vstar (fun _ => Set.univ) (fun x y => qF a b c (x, y)) δ x₀ := by
  set K := δ * Q + c with hKdef
  have hK : 0 < K := by positivity
  have hFle : ∀ x y, qF a b c (x, y) ≤ a ^ 2 / (2 * b) := fun x y => by
    simp only [qF]
    have e : a ^ 2 / (2 * b) - (a * x - b * x ^ 2 / 2) = (b * x - a) ^ 2 / (2 * b) := by
      field_simp; ring
    have : 0 ≤ (b * x - a) ^ 2 / (2 * b) := by positivity
    nlinarith [sq_nonneg (y - x)]
  have h42 : Assumption42 (fun _ => Set.univ) (fun x y => qF a b c (x, y)) δ :=
    assumption42_of_bddAbove (fun x y => hFle x y) hδ0.le hδ1
  -- the plan is bounded: it contracts towards `P/Q`
  have hs1 : c / K ≤ 1 := by rw [div_le_one hK]; nlinarith
  have hstep : ∀ t, x (t + 1) - P / Q = c / K * (x t - P / Q) := fun t => by
    rw [hx t]
    have hb' : b * K = Q * K - δ * Q * c := by
      have := hQ; field_simp at this; linarith
    field_simp
    ring_nf
    nlinarith [hb']
  have hxb : ∀ t, |x t - P / Q| ≤ |x₀ - P / Q| := by
    intro t
    induction t with
    | zero => rw [hx0]
    | succ t ih =>
      rw [hstep, abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs1).trans ih
  set M := |P / Q| + |x₀ - P / Q|
  have hxM : ∀ t, |x t| ≤ M := fun t => by
    have := hxb t
    calc |x t| = |(x t - P / Q) + P / Q| := by ring_nf
      _ ≤ |x t - P / Q| + |P / Q| := abs_add_le _ _
      _ ≤ M := by simp only [M]; linarith
  refine euler_sufficient h42 ⟨hx0, fun _ => Set.mem_univ _⟩
    (fun t => qD a b c (x t) (x (t + 1))) (fun t x y _ => qF_le hb hc x y _ _)
    (fun t v => ?_) hδ0.le (fun y hy hbot => ?_)
  · -- the Euler equation along the linear policy
    rw [qFy, qFx, hx (t + 1), hx t]
    have ha2 : a = P - δ * P * c / K := by linarith
    have hb2 : b = Q - δ * Q * c / K := by linarith
    have hne : δ * Q + c ≠ 0 := hK.ne'
    rw [ha2, hb2, hKdef]
    field_simp
    ring
  · -- against a plan with `u(y) > −∞`, `Σ δᵗy_t² < ∞`, so `δᵗy_t → 0`
    have hFsq : ∀ u w, qF a b c (u, w) ≤ a ^ 2 / b - b / 4 * u ^ 2 := fun u w => by
      simp only [qF]
      have e : a ^ 2 / b - a * u + b * u ^ 2 / 4 = (2 * a - b * u) ^ 2 / (4 * b) := by
        field_simp; ring
      have : 0 ≤ (2 * a - b * u) ^ 2 / (4 * b) := by positivity
      nlinarith [sq_nonneg (w - u)]
    have hsum : Summable fun t => δ ^ t * y t ^ 2 := by
      by_contra hns
      have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
        (fun t => mul_nonneg (pow_nonneg hδ0.le t) (sq_nonneg (y t)))).1 hns
      -- then `u_T(y) → −∞`
      have hbound : ∀ T, partialSum (fun x y => qF a b c (x, y)) δ y T ≤
          a ^ 2 / (b * (1 - δ)) - b / 4 * ∑ t ∈ Finset.range (T + 1), δ ^ t * y t ^ 2 := by
        intro T
        have h1 : partialSum (fun x y => qF a b c (x, y)) δ y T ≤
            ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b - b / 4 * y t ^ 2) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hFsq _ _)
            (pow_nonneg hδ0.le t)
        have h2 : ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b) ≤ a ^ 2 / (b * (1 - δ)) := by
          rw [← Finset.sum_mul]
          calc (∑ t ∈ Finset.range (T + 1), δ ^ t) * (a ^ 2 / b)
              ≤ (∑' t, δ ^ t) * (a ^ 2 / b) := mul_le_mul_of_nonneg_right
                ((summable_geometric_of_lt_one hδ0.le hδ1).sum_le_tsum _
                  fun t _ => pow_nonneg hδ0.le t) (by positivity)
            _ = a ^ 2 / (b * (1 - δ)) := by
                rw [tsum_geometric_of_lt_one hδ0.le hδ1]
                have : (1 - δ) ≠ 0 := by linarith
                field_simp
        have e : ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b - b / 4 * y t ^ 2) =
            ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b) -
              b / 4 * ∑ t ∈ Finset.range (T + 1), δ ^ t * y t ^ 2 := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun t _ => by ring
        linarith
      have hQ := ((hdiv.comp (tendsto_add_atTop_nat 1)).const_mul_atTop
        (by positivity : (0 : ℝ) < b / 4))
      have hlow : Tendsto (fun T => a ^ 2 / (b * (1 - δ)) - b / 4 *
          ∑ t ∈ Finset.range (T + 1), δ ^ t * y t ^ 2) atTop atBot := by
        simp only [sub_eq_add_neg]
        exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp hQ)
      have hneg : Tendsto (fun T => partialSum (fun x y => qF a b c (x, y)) δ y T) atTop
          atBot := tendsto_atBot_mono hbound hlow
      exact hbot (tendsto_nhds_unique (tendsto_total h42 hy)
        (EReal.tendsto_coe_atBot.comp hneg))
    -- `δᵗ|y_t| → 0`
    have hsq := hsum.tendsto_atTop_zero
    have hz : Tendsto (fun t => δ ^ t * |y t|) atTop (𝓝 0) := by
      have hsqrt := ((Real.continuous_sqrt.tendsto 0).comp hsq)
      rw [Real.sqrt_zero] at hsqrt
      refine squeeze_zero (fun t => by positivity) (fun t => ?_) hsqrt
      simp only [Function.comp_apply]
      rw [← Real.sqrt_sq (by positivity : 0 ≤ δ ^ t * |y t|)]
      refine Real.sqrt_le_sqrt ?_
      rw [mul_pow, sq_abs, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hδ0.le hδ1.le (by omega))
        (sq_nonneg _)
    -- the bound on `F_x` along the policy plan
    set Cf := |a| + b * M + 2 * c * M
    have hf : ∀ t, |a - b * x t + c * (x (t + 1) - x t)| ≤ Cf := fun t => by
      have h1 := hxM t
      have h2 := hxM (t + 1)
      calc |a - b * x t + c * (x (t + 1) - x t)|
          ≤ |a| + b * |x t| + c * (|x (t + 1)| + |x t|) := by
            refine (abs_add_le _ _).trans ?_
            refine add_le_add ((abs_sub _ _).trans ?_) ?_
            · rw [abs_mul, abs_of_pos hb]
            · rw [abs_mul, abs_of_pos hc]
              exact mul_le_mul_of_nonneg_left (abs_sub _ _) hc.le
        _ ≤ Cf := by simp only [Cf]; nlinarith
    refine ⟨fun T => Cf * (δ ^ (T + 1) * M + δ ^ (T + 1) * |y (T + 1)|), ?_, fun T => ?_⟩
    · have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).comp
        (tendsto_add_atTop_nat 1)
      have h2 := hz.comp (tendsto_add_atTop_nat 1)
      have := ((h1.mul_const M).add h2).const_mul Cf
      simpa [Function.comp_def] using this
    · rw [qFx]
      have hδp : 0 ≤ δ ^ (T + 1) := pow_nonneg hδ0.le _
      calc δ ^ (T + 1) * ((a - b * x (T + 1) + c * (x (T + 1 + 1) - x (T + 1))) *
            (x (T + 1) - y (T + 1)))
          ≤ δ ^ (T + 1) * (Cf * (M + |y (T + 1)|)) := by
            refine mul_le_mul_of_nonneg_left ?_ hδp
            refine (le_abs_self _).trans ?_
            rw [abs_mul]
            refine mul_le_mul (hf _) ((abs_sub _ _).trans (add_le_add (hxM _) le_rfl))
              (abs_nonneg _) (by simp only [Cf]; positivity)
        _ = Cf * (δ ^ (T + 1) * M + δ ^ (T + 1) * |y (T + 1)|) := by ring

end StokeyLucasPrescott.DeterministicDP

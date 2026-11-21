/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DifferenceEquations.PhaseDiagram

/-!
# Exercises of Chapter 1

Miao, §1.8, pp. 41–43. Exercises 3 and 4 are Dynare exercises and are not formalised.

**Exercise 1 (Cagan).** `m_t − p_t = −α(p_{t+1} − p_t)`, `α > 0` (`IsCagan`), which is (1.1)
with `b = (1 + α)/α > 1` (`cagan_isScalarSol`).
* (a), `ρ ∈ [0, 1)`: for every `μ` and `m₀` there is a unique bounded solution,
  `p_t = m̄ + (m_t − m̄)/(1 + α(1 − ρ))`, `m̄ = μ/(1 − ρ)` (`ex_1_1a`), equal to the forward sum
  `(1/(1 + α)) Σ (α/(1 + α))ʲ m_{t+j}` (`ex_1_1a_forward`).
* (a), `ρ = 1`: a bounded solution exists iff `μ = 0` (`ex_1_1a_rho_one_bdd_iff`); for every `μ`
  the unique solution with `p_t − m_t` bounded is `p_t = m_t + αμ` (`ex_1_1a_rho_one`).
* (b): the announced increase `m_t = m̄` (`t < T`), `m̄'` (`t ≥ T`): the unique bounded path is
  `p_t = m̄ + (α/(1 + α))^{T−t}(m̄' − m̄)` for `t ≤ T` and `m̄'` after (`cagan_path`,
  `ex_1_1b_solves`, `ex_1_1b_unique`); the price jumps at the announcement and rises strictly
  to `m̄'` at `T`, staying above money before `T` (`ex_1_1b_shape`).

**Exercise 2 (Dornbusch).** The four equations (`IsDornbusch`) reduce to a forward recursion in
`(e_t, p_t)` (`ex_1_2_reduce`, `IsDorn2`).
* (a) The steady state `r = r*`, `y^d = y`, `p̄ = m̄ − αy + βr*`,
  `ē = p̄ − p* + ((1 − φ)y + γr* − g)/δ` (`ex_1_2a`).
* (b) Deviations solve the 2×2 system `[[1 − θ(δ + γ/β), θδ], [1/β, 1]]` (`ex_1_2_dev`) with
  `p(1) = −θδ/β < 0` and `p(−1) = 4 − θ(2δ + (2γ + δ)/β)`. With `p` predetermined and `e` a jump
  variable, every `p₀` has a (unique) convergent path iff `θ(2δ + (2γ + δ)/β) < 4`
  (`ex_1_2b_iff`); under this condition the bounded path through `p₀` is unique and all others
  are unbounded (`ex_1_2b_unique`). The condition is not automatic in discrete time
  (`ex_1_2b_counterexample`).
* (c) Isoclines: `Δe ≥ 0 ⟺ p ≥ p̄` and `Δp ≥ 0 ⟺ (δ + γ/β)(p − p̄) ≤ δ(e − ē)` (`ex_1_2c`).
* (d) The unexpected permanent increase `m̄ → m̄'` at date 0 from the old steady state: the
  unique bounded path is `p_t = p̄' − λᵗΔm`, `e_t = ē' − kλᵗΔm` (`ex_1_2d_path`,
  `ex_1_2d_unique`); the exchange rate overshoots, `e₀ − ē = (1 − k)Δm > Δm` (`ex_1_2d_overshoot`),
  and for `λ > 0` the price rises and the exchange rate falls monotonically (`ex_1_2d_monotone`).
* (e) The announced increase at `T`: any bounded path from the old steady state has
  `e₀ = ē + λ_hi^{−T}(1 + (1/β)/(λ_hi − m₁₁))Δm` (`ex_1_2e_jump`); this path exists, is bounded
  and converges to the new steady state (`ex_1_2e_exists`); the jump is positive and strictly
  decreasing in `T`, and equals the jump in (d) at `T = 0` (`ex_1_2e_jump_shape`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-! ### Exercise 1: the Cagan model -/

/-- The Cagan model under perfect foresight (Miao, Exercise 1, p. 41):
`m_t − p_t = −α(p_{t+1} − p_t)`. -/
def IsCagan (α : ℝ) (m p : ℕ → ℝ) : Prop :=
  ∀ t, m t - p t = -α * (p (t + 1) - p t)

/-- The Cagan model is (1.1) with `b = (1 + α)/α`, `c = −1/α`, `z = m`. -/
theorem cagan_isScalarSol {α : ℝ} (hα : 0 < α) {m p : ℕ → ℝ} :
    IsCagan α m p ↔ IsScalarSol ((1 + α) / α) (-1 / α) m p := by
  simp only [IsCagan, IsScalarSol]
  refine forall_congr' fun t => ?_
  constructor
  · intro h; field_simp; linarith
  · intro h; field_simp at h; linarith

theorem cagan_b_gt_one {α : ℝ} (hα : 0 < α) : 1 < |(1 + α) / α| := by
  rw [abs_of_pos (by positivity), lt_div_iff₀ hα]
  linarith

/-- **Exercise 1(a)** (Miao, p. 41), `ρ ∈ [0, 1)`: for `α > 0`, every `μ` and every `m₀`, the
Cagan model has a unique stable (bounded) solution,
`p_t = m̄ + (m_t − m̄)/(1 + α(1 − ρ))` with `m̄ = μ/(1 − ρ)`. -/
theorem ex_1_1a {α ρ μ : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {m : ℕ → ℝ}
    (hm : ∀ t, m (t + 1) = ρ * m t + μ) :
    IsCagan α m (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) ∧
      BddSeq (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) ∧
      ∀ p, IsCagan α m p → BddSeq p →
        p = fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ)) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + α * (1 - ρ) := by positivity
  have hmB : BddSeq m :=
    eq_1_5_bdd (b := ρ) (c := μ) (z := fun _ => 1) (by rw [abs_of_nonneg hρ0]; exact hρ1)
      ⟨1, fun _ => by simp⟩ (fun t => by rw [hm t, mul_one])
  have hsol : IsCagan α m (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) := by
    intro t
    simp only
    rw [hm t]
    field_simp
    ring
  have hB : BddSeq (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) := by
    obtain ⟨M, hM⟩ := hmB
    refine ⟨|μ / (1 - ρ)| + (M + |μ / (1 - ρ)|) / (1 + α * (1 - ρ)), fun t => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_div, abs_of_pos h2]
    exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hM t) le_rfl)) h2.le
  refine ⟨hsol, hB, fun p hp hpB => ?_⟩
  have hb := cagan_b_gt_one hα
  rw [eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 hp) hpB,
    eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 hsol) hB]

/-- **Exercise 1(a)** (Miao, p. 41): the stable solution is the forward solution
`p_t = (1/(1 + α)) Σ_{j≥0} (α/(1 + α))ʲ m_{t+j}` (this is (1.8) for the Cagan model). -/
theorem ex_1_1a_forward {α : ℝ} (hα : 0 < α) (m : ℕ → ℝ) (t : ℕ) :
    fwdSol ((1 + α) / α) (-1 / α) m t =
      1 / (1 + α) * ∑' j : ℕ, (α / (1 + α)) ^ j * m (t + j) := by
  have : (1 : ℝ) / ((1 + α) / α) = α / (1 + α) := by rw [one_div_div]
  simp only [fwdSol, this]
  congr 1
  field_simp

/-- **Exercise 1(a)** (Miao, p. 41), `ρ = 1`: with `m_{t+1} = m_t + μ` a stable (bounded)
solution exists iff `μ = 0`; money grows without bound otherwise. -/
theorem ex_1_1a_rho_one_bdd_iff {α μ : ℝ} (hα : 0 < α) {m : ℕ → ℝ}
    (hm : ∀ t, m (t + 1) = m t + μ) :
    (∃ p, IsCagan α m p ∧ BddSeq p) ↔ μ = 0 := by
  have hform : ∀ t, m t = m 0 + μ * t := fun t => by
    induction t with
    | zero => simp
    | succ n ih => rw [hm n, ih]; push_cast; ring
  constructor
  · rintro ⟨p, hp, ⟨M, hM⟩⟩
    by_contra hμ
    have hmB : ∀ t, |m t| ≤ M + α * (M + M) := fun t => by
      have := hp t
      have e : m t = p t - α * (p (t + 1) - p t) := by linarith
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hM t) ?_)
      rw [abs_mul, abs_of_pos hα]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM _) (hM t))) hα.le
    have hlim : Tendsto (fun t : ℕ => |m 0 + μ * t|) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (abs_pos.2 hμ)
      refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-|m 0|) h)
      have := abs_sub_abs_le_abs_sub (μ * t) (-m 0)
      rw [abs_neg, sub_neg_eq_add, abs_mul, Nat.abs_cast, add_comm (μ * t)] at this
      linarith
    obtain ⟨t, ht⟩ := (hlim.eventually_gt_atTop (M + α * (M + M))).exists
    rw [← hform t] at ht
    linarith [hmB t]
  · rintro rfl
    refine ⟨m, fun t => by rw [hm t]; ring, ⟨|m 0|, fun t => by rw [hform t]; simp⟩⟩

/-- **Exercise 1(a)** (Miao, p. 41), `ρ = 1`, corrected statement: for every `μ` the unique
solution with `p_t − m_t` bounded (no bubble in real balances) is `p_t = m_t + αμ`. -/
theorem ex_1_1a_rho_one {α μ : ℝ} (hα : 0 < α) {m : ℕ → ℝ} (hm : ∀ t, m (t + 1) = m t + μ) :
    IsCagan α m (fun t => m t + α * μ) ∧
      ∀ p, IsCagan α m p → BddSeq (fun t => p t - m t) → p = fun t => m t + α * μ := by
  refine ⟨fun t => by simp only; rw [hm t]; ring, fun p hp hB => ?_⟩
  have hq : IsScalarSol ((1 + α) / α) (-μ) (fun _ => 1) (fun t => p t - m t) := by
    intro t
    have := hp t
    simp only
    rw [hm t]
    field_simp
    linarith
  have := (eq_1_3_bdd_iff (cagan_b_gt_one hα) hq).1 hB
  have hbar : -μ / (1 - (1 + α) / α) = α * μ := by field_simp; ring
  ext t
  have := this t
  rw [hbar] at this
  linarith

/-- The announced money path of Exercise 1(b): `m̄` before `T`, `m̄'` from `T` on. -/
def cagan_money (mb mb' : ℝ) (T t : ℕ) : ℝ :=
  if t < T then mb else mb'

/-- The price path of Exercise 1(b): `p_t = m̄ + (α/(1 + α))^{T−t}(m̄' − m̄)` for `t ≤ T`,
`p_t = m̄'` for `t ≥ T`. -/
noncomputable def cagan_path (α mb mb' : ℝ) (T t : ℕ) : ℝ :=
  if t ≤ T then mb + (α / (1 + α)) ^ (T - t) * (mb' - mb) else mb'

/-- **Exercise 1(b)** (Miao, p. 41): the price path solves the Cagan model with the announced
money path. -/
theorem ex_1_1b_solves {α mb mb' : ℝ} (hα : 0 < α) (T : ℕ) :
    IsCagan α (cagan_money mb mb' T) (cagan_path α mb mb' T) := by
  intro t
  have h1 : (1 + α) ≠ 0 := by positivity
  rcases lt_trichotomy (t + 1) (T + 1) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, T = t + 1 + k := ⟨T - (t + 1), by omega⟩
    simp only [cagan_money, cagan_path, show t < t + 1 + k by omega, show t ≤ t + 1 + k by omega,
      show t + 1 ≤ t + 1 + k by omega, ↓reduceIte, show t + 1 + k - t = k + 1 by omega,
      show t + 1 + k - (t + 1) = k by omega, pow_succ]
    field_simp
    ring
  · obtain rfl : t = T := by omega
    simp only [cagan_money, cagan_path, lt_irrefl, le_refl, show ¬ t + 1 ≤ t by omega,
      ↓reduceIte, Nat.sub_self, pow_zero, one_mul]
    ring
  · simp only [cagan_money, cagan_path, show ¬ t < T by omega, show ¬ t ≤ T by omega,
      show ¬ t + 1 ≤ T by omega, ↓reduceIte]
    ring

theorem cagan_path_const {α mb mb' : ℝ} {T t : ℕ} (ht : T ≤ t) :
    cagan_path α mb mb' T t = mb' := by
  rcases ht.lt_or_eq with h | rfl
  · simp only [cagan_path, show ¬ t ≤ T by omega, ↓reduceIte]
  · simp only [cagan_path, le_refl, ↓reduceIte, Nat.sub_self, pow_zero, one_mul]
    ring

/-- **Exercise 1(b)** (Miao, p. 41): the price path is the unique bounded solution. -/
theorem ex_1_1b_unique {α mb mb' : ℝ} (hα : 0 < α) (T : ℕ) {p : ℕ → ℝ}
    (hp : IsCagan α (cagan_money mb mb' T) p) (hB : BddSeq p) : p = cagan_path α mb mb' T := by
  have hb := cagan_b_gt_one hα
  have hmB : BddSeq (cagan_money mb mb' T) :=
    ⟨|mb| + |mb'|, fun t => by
      simp only [cagan_money]; split_ifs
      · linarith [abs_nonneg mb']
      · linarith [abs_nonneg mb]⟩
  have hpathB : BddSeq (cagan_path α mb mb' T) :=
    bddSeq_of_tendsto (L := mb') (tendsto_const_nhds.congr'
      (eventually_atTop.2 ⟨T, fun t ht => (cagan_path_const ht).symm⟩))
  rw [eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 hp) hB,
    eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 (ex_1_1b_solves hα T)) hpathB]

/-- **Exercise 1(b)** (Miao, p. 41): for `m̄' > m̄` the price jumps at the announcement
(`p₀ > m̄` when `T > 0`, i.e. above the pre-announcement price `m̄`), rises strictly until `T`,
stays above the money supply before `T`, and equals `m̄'` from `T` on. -/
theorem ex_1_1b_shape {α mb mb' : ℝ} (hα : 0 < α) (hm : mb < mb') (T : ℕ) :
    mb < cagan_path α mb mb' T 0 ∧
      (∀ t, t < T → cagan_path α mb mb' T t < cagan_path α mb mb' T (t + 1)) ∧
      (∀ t, t < T → cagan_money mb mb' T t < cagan_path α mb mb' T t) ∧
      ∀ t, T ≤ t → cagan_path α mb mb' T t = mb' := by
  have hq0 : 0 < α / (1 + α) := by positivity
  have hq1 : α / (1 + α) < 1 := by rw [div_lt_one (by positivity)]; linarith
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t ht => cagan_path_const ht⟩
  · simp only [cagan_path, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    have : 0 < (α / (1 + α)) ^ T * (mb' - mb) := mul_pos (pow_pos hq0 T) (by linarith)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, T = t + 1 + k := ⟨T - (t + 1), by omega⟩
    simp only [cagan_path, show t ≤ t + 1 + k by omega, show t + 1 ≤ t + 1 + k by omega,
      ↓reduceIte, show t + 1 + k - t = k + 1 by omega, show t + 1 + k - (t + 1) = k by omega,
      pow_succ]
    have hk := pow_pos hq0 k
    have : (α / (1 + α)) ^ k * (α / (1 + α)) < (α / (1 + α)) ^ k := by
      nlinarith
    nlinarith
  · simp only [cagan_money, cagan_path, ht, ↓reduceIte, ht.le]
    have : 0 < (α / (1 + α)) ^ (T - t) * (mb' - mb) := mul_pos (pow_pos hq0 _) (by linarith)
    linarith

/-! ### Exercise 2: the Dornbusch model -/

/-- The Dornbusch model (Miao, Exercise 2, p. 42):
`y^d_t = δ(e_t + p* − p_t) − γr_t + φy + g`, `p_{t+1} − p_t = θ(y^d_t − y)`,
`m_t − p_t = αy − βr_t`, `r_t = r* + e_{t+1} − e_t`. -/
def IsDornbusch (δ γ φ θ α β y g ps rs : ℝ) (m yd e p r : ℕ → ℝ) : Prop :=
  ∀ t, yd t = δ * (e t + ps - p t) - γ * r t + φ * y + g ∧ p (t + 1) - p t = θ * (yd t - y) ∧
    m t - p t = α * y - β * r t ∧ r t = rs + e (t + 1) - e t

/-- The reduced forward recursion of the Dornbusch model in `(e_t, p_t)`. -/
def IsDorn2 (δ γ φ θ α β y g ps rs : ℝ) (m e p : ℕ → ℝ) : Prop :=
  ∀ t, e (t + 1) = e t + (α * y - m t + p t) / β - rs ∧
    p (t + 1) = p t + θ * (δ * (e t + ps - p t) - γ * ((α * y - m t + p t) / β) + φ * y + g - y)

/-- The steady-state price `p̄ = m̄ − αy + βr*`. -/
def pbarD (α β y rs mb : ℝ) : ℝ := mb - α * y + β * rs

/-- The steady-state exchange rate `ē = p̄ − p* + ((1 − φ)y + γr* − g)/δ`. -/
noncomputable def ebarD (δ γ φ α β y g ps rs mb : ℝ) : ℝ :=
  pbarD α β y rs mb - ps + ((1 - φ) * y + γ * rs - g) / δ

/-- The `(p, p)` entry `1 − θ(δ + γ/β)` of the Dornbusch coefficient matrix. -/
noncomputable def dM11 (θ δ γ β : ℝ) : ℝ := 1 - θ * (δ + γ / β)

/-- The stable root of the Dornbusch matrix `[[1 − θ(δ + γ/β), θδ], [1/β, 1]]`. -/
noncomputable abbrev dLo (θ δ γ β : ℝ) : ℝ := lamLo (dM11 θ δ γ β) (θ * δ) (1 / β) 1

/-- The unstable root of the Dornbusch matrix. -/
noncomputable abbrev dHi (θ δ γ β : ℝ) : ℝ := lamHi (dM11 θ δ γ β) (θ * δ) (1 / β) 1

/-- The slope `k = (λ_lo − m₁₁)/(θδ)` of the Dornbusch saddle path in `(p − p̄, e − ē)`. -/
noncomputable abbrev dK (θ δ γ β : ℝ) : ℝ := kSaddle (dM11 θ δ γ β) (θ * δ) (1 / β) 1

/-- Forward iteration of the reduced Dornbusch recursion from `(e₀, p₀)`. -/
noncomputable def dornIter (δ γ φ θ α β y g ps rs : ℝ) (m : ℕ → ℝ) (e0 p0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (e0, p0)
  | t + 1 => ((dornIter δ γ φ θ α β y g ps rs m e0 p0 t).1 +
      (α * y - m t + (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) / β - rs,
    (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2 + θ * (δ * ((dornIter δ γ φ θ α β y g ps rs m e0
      p0 t).1 + ps - (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) - γ * ((α * y - m t +
      (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) / β) + φ * y + g - y))

variable {δ γ φ θ α β y g ps rs : ℝ}

theorem dornIter_sol (m : ℕ → ℝ) (e0 p0 : ℝ) :
    IsDorn2 δ γ φ θ α β y g ps rs m (fun t => (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).1)
      (fun t => (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) := fun _ => ⟨rfl, rfl⟩

/-- **Exercise 2** (Miao, p. 42): the four equations are equivalent to `r_t`, `y^d_t` given by
the money market and demand equations plus the forward recursion `IsDorn2` in `(e, p)`. -/
theorem ex_1_2_reduce (hβ : β ≠ 0) (m yd e p r : ℕ → ℝ) :
    IsDornbusch δ γ φ θ α β y g ps rs m yd e p r ↔
      (∀ t, r t = (α * y - m t + p t) / β ∧ yd t = δ * (e t + ps - p t) - γ * r t + φ * y + g) ∧
        IsDorn2 δ γ φ θ α β y g ps rs m e p := by
  constructor
  · intro h
    have hr : ∀ t, r t = (α * y - m t + p t) / β := fun t => by
      rw [eq_div_iff hβ]; linarith [(h t).2.2.1]
    refine ⟨fun t => ⟨hr t, (h t).1⟩, fun t => ⟨?_, ?_⟩⟩
    · rw [← hr t]; linarith [(h t).2.2.2]
    · rw [← hr t]; have := (h t).2.1; rw [(h t).1] at this; linarith
  · rintro ⟨h1, h2⟩ t
    refine ⟨(h1 t).2, ?_, ?_, ?_⟩
    · rw [(h2 t).2, (h1 t).2, (h1 t).1]; ring
    · rw [(h1 t).1]; field_simp; ring
    · rw [(h2 t).1, (h1 t).1]; ring

/-- **Exercise 2(a)** (Miao, p. 43): with constant money `m̄`, a constant `(y^d, e, p, r)` solves
the model iff `r = r*`, `y^d = y`, `p = p̄ = m̄ − αy + βr*` and
`e = ē = p̄ − p* + ((1 − φ)y + γr* − g)/δ`. -/
theorem ex_1_2a (hδ : δ ≠ 0) (hθ : θ ≠ 0) (mb ydb eb pb rb : ℝ) :
    IsDornbusch δ γ φ θ α β y g ps rs (fun _ => mb) (fun _ => ydb) (fun _ => eb) (fun _ => pb)
        (fun _ => rb) ↔
      rb = rs ∧ ydb = y ∧ pb = pbarD α β y rs mb ∧ eb = ebarD δ γ φ α β y g ps rs mb := by
  simp only [IsDornbusch, pbarD, ebarD]
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h 0
    have hr : rb = rs := by linarith
    have hyd : ydb = y := by
      have : θ * (ydb - y) = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hθ
      linarith
    have hp : pb = mb - α * y + β * rs := by rw [← hr]; linarith
    refine ⟨hr, hyd, hp, ?_⟩
    rw [hr, hyd, hp] at h1
    field_simp
    linarith
  · rintro ⟨rfl, rfl, rfl, rfl⟩ _
    refine ⟨?_, by ring, by ring, by ring⟩
    field_simp
    ring

/-- **Exercise 2** (Miao, p. 43): when `m_t = m_c`, the deviations from the steady state
`(p̄(m_c), ē(m_c))` move one step by the matrix `[[1 − θ(δ + γ/β), θδ], [1/β, 1]]`. -/
theorem ex_1_2_dev_step (hδ : δ ≠ 0) (hβ : β ≠ 0) {m e p : ℕ → ℝ} {mc : ℝ} {t : ℕ}
    (hm : m t = mc) :
    (e (t + 1) = e t + (α * y - m t + p t) / β - rs ∧
      p (t + 1) = p t + θ * (δ * (e t + ps - p t) - γ * ((α * y - m t + p t) / β) + φ * y + g
        - y)) ↔
    (p (t + 1) - pbarD α β y rs mc = dM11 θ δ γ β * (p t - pbarD α β y rs mc) +
        θ * δ * (e t - ebarD δ γ φ α β y g ps rs mc) ∧
      e (t + 1) - ebarD δ γ φ α β y g ps rs mc = 1 / β * (p t - pbarD α β y rs mc) +
        1 * (e t - ebarD δ γ φ α β y g ps rs mc)) := by
  rw [hm]
  have i1 : θ * (δ * (e t + ps - p t) - γ * ((α * y - mc + p t) / β) + φ * y + g - y) =
      (dM11 θ δ γ β - 1) * (p t - pbarD α β y rs mc) +
        θ * δ * (e t - ebarD δ γ φ α β y g ps rs mc) := by
    simp only [dM11, ebarD, pbarD]; field_simp; ring
  have i2 : e t + (α * y - mc + p t) / β - rs = e t + 1 / β * (p t - pbarD α β y rs mc) := by
    simp only [pbarD]; field_simp; ring
  rw [i1, i2]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [h2]; ring
    · rw [h1]; ring
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **Exercise 2(b)** (Miao, p. 43): with constant money the deviations solve the 2×2 system. -/
theorem ex_1_2_dev (hδ : δ ≠ 0) (hβ : β ≠ 0) (mb : ℝ) (e p : ℕ → ℝ) :
    IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p ↔
      IsSol22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (fun t => p t - pbarD α β y rs mb)
        (fun t => e t - ebarD δ γ φ α β y g ps rs mb) :=
  forall_congr' fun _ => ex_1_2_dev_step (m := fun _ => mb) hδ hβ rfl

theorem dorn_cp_one (hβ : β ≠ 0) :
    cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 1 = -(θ * δ / β) := by
  simp only [cp22, dM11]; field_simp; ring

/-- **Exercise 2(b)** (Miao, p. 43): `p(−1) = 4 − θ(2δ + (2γ + δ)/β)`. -/
theorem dorn_cp_neg_one (hβ : β ≠ 0) :
    cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (-1) = 4 - θ * (2 * δ + (2 * γ + δ) / β) := by
  simp only [cp22, dM11]; field_simp; ring

theorem dorn_h1 (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) :
    cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 1 < 0 := by
  rw [dorn_cp_one hβ.ne']
  have : 0 < θ * δ / β := by positivity
  linarith

theorem dorn_hm (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) : 0 < θ * δ * (1 / β) := by positivity

/-- Under `θ(2δ + (2γ + δ)/β) < 4`, a path on the saddle line converges to the steady state. -/
theorem dorn_tendsto (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p)
    (hk : e 0 - ebarD δ γ φ α β y g ps rs mb = dK θ δ γ β * (p 0 - pbarD α β y rs mb)) :
    Tendsto p atTop (𝓝 (pbarD α β y rs mb)) ∧
      Tendsto e atTop (𝓝 (ebarD δ γ φ α β y g ps rs mb)) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hc : 0 < cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (-1) := by
    rw [dorn_cp_neg_one hβ.ne']; linarith
  have hdev := (ex_1_2_dev hδ.ne' hβ.ne' mb e p).1 h
  obtain ⟨hX, hY⟩ := hdev.ext (saddle22 h1 (by positivity) (p 0 - pbarD α β y rs mb))
    (by simp) (by simp only [pow_zero, one_mul]; exact hk)
  obtain ⟨t1, t2⟩ := saddle22_tendsto h1 hc (p 0 - pbarD α β y rs mb)
  rw [← hX] at t1
  rw [← hY] at t2
  exact ⟨by simpa using t1.add_const (pbarD α β y rs mb),
    by simpa using t2.add_const (ebarD δ γ φ α β y g ps rs mb)⟩

/-- **Exercise 2(b)** (Miao, p. 43): with `p` predetermined and `e` a jump variable, every `p₀`
has a path converging to the steady state iff `θ(2δ + (2γ + δ)/β) < 4` (equivalently the stable
root lies in `(−1, 1)`; the other root always exceeds `1`). -/
theorem ex_1_2b_iff (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) (mb : ℝ) :
    (∀ p0, ∃ e p : ℕ → ℝ, IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p ∧ p 0 = p0 ∧
      Tendsto p atTop (𝓝 (pbarD α β y rs mb)) ∧
      Tendsto e atTop (𝓝 (ebarD δ γ φ α β y g ps rs mb))) ↔
      θ * (2 * δ + (2 * γ + δ) / β) < 4 := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  constructor
  · intro H
    have := (saddle22_iff h1 (dorn_hm hδ hθ hβ)).1 (fun X0 => by
      obtain ⟨e, p, h, hp0, hp, he⟩ := H (X0 + pbarD α β y rs mb)
      exact ⟨_, _, (ex_1_2_dev hδ.ne' hβ.ne' mb e p).1 h, by simp [hp0],
        by simpa using hp.sub_const (pbarD α β y rs mb),
        by simpa using he.sub_const (ebarD δ γ φ α β y g ps rs mb)⟩)
    rw [dorn_cp_neg_one hβ.ne'] at this
    linarith
  · intro hcond p0
    set e0 := ebarD δ γ φ α β y g ps rs mb + dK θ δ γ β * (p0 - pbarD α β y rs mb)
    have hsol := dornIter_sol (δ := δ) (γ := γ) (φ := φ) (θ := θ) (α := α) (β := β) (y := y)
      (g := g) (ps := ps) (rs := rs) (fun _ => mb) e0 p0
    refine ⟨_, _, hsol, rfl, dorn_tendsto hδ hθ hβ hcond hsol ?_⟩
    simp only [dornIter, e0]
    ring

/-- **Exercise 2(b)** (Miao, p. 43): under `θ(2δ + (2γ + δ)/β) < 4` a path is bounded iff it
starts on the saddle line `e₀ − ē = k(p₀ − p̄)`; so for given `p₀` the stable solution is unique
(`e₀` jumps onto the line) and every other path is unbounded. -/
theorem ex_1_2b_unique (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p) :
    (BddSeq p ∧ BddSeq e) ↔
      e 0 - ebarD δ γ φ α β y g ps rs mb = dK θ δ γ β * (p 0 - pbarD α β y rs mb) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hm := dorn_hm hδ hθ hβ
  have hdev := (ex_1_2_dev hδ.ne' hβ.ne' mb e p).1 h
  constructor
  · rintro ⟨hp, he⟩
    exact (sHi_zero_iff h1 hm _ _ 0).1 (sHi_zero_of_bdd h1 hdev
      (bddSeq_sub_const hp _) (bddSeq_sub_const he _))
  · intro hk
    obtain ⟨t1, t2⟩ := dorn_tendsto hδ hθ hβ hcond h hk
    exact ⟨bddSeq_of_tendsto t1, bddSeq_of_tendsto t2⟩

/-- **Exercise 2(b)** (Miao, p. 43): the stability condition is not automatic in discrete time.
For `δ = γ = β = θ = 1`, `θ(2δ + (2γ + δ)/β) = 5 > 4`, both roots are unstable, and the steady
state is the only bounded path. -/
theorem ex_1_2b_counterexample {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 1 1 φ 1 α 1 y g ps rs (fun _ => mb) e p) (hp : BddSeq p) (he : BddSeq e) :
    (1 : ℝ) * (2 * 1 + (2 * 1 + 1) / 1) = 5 ∧
      p = (fun _ => pbarD α 1 y rs mb) ∧ e = (fun _ => ebarD 1 1 φ α 1 y g ps rs mb) := by
  have h1 := dorn_h1 (δ := 1) (θ := 1) (β := 1) (γ := 1) one_pos one_pos one_pos
  have hc : cp22 (dM11 1 1 1 1) (1 * 1) (1 / 1) 1 (-1) < 0 := by
    rw [dorn_cp_neg_one one_ne_zero]; norm_num
  obtain ⟨hX, hY⟩ := saddle22_only_zero h1 (dorn_hm one_pos one_pos one_pos) hc
    ((ex_1_2_dev one_ne_zero one_ne_zero mb e p).1 h) (bddSeq_sub_const hp _)
    (bddSeq_sub_const he _)
  refine ⟨by norm_num, ?_, ?_⟩
  · ext t; have := congrFun hX t; simp only [Pi.zero_apply] at this; linarith
  · ext t; have := congrFun hY t; simp only [Pi.zero_apply] at this; linarith

/-- **Exercise 2(c)** (Miao, p. 43), the phase-diagram isoclines: with constant money,
`Δe_t ≥ 0 ⟺ p_t ≥ p̄` and `Δp_t ≥ 0 ⟺ (δ + γ/β)(p_t − p̄) ≤ δ(e_t − ē)`. -/
theorem ex_1_2c (hδ : δ ≠ 0) (hθ : 0 < θ) (hβ : 0 < β) {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p) (t : ℕ) :
    (0 ≤ e (t + 1) - e t ↔ pbarD α β y rs mb ≤ p t) ∧
      (0 ≤ p (t + 1) - p t ↔
        (δ + γ / β) * (p t - pbarD α β y rs mb) ≤ δ * (e t - ebarD δ γ φ α β y g ps rs mb)) := by
  obtain ⟨h1, h2⟩ := ((ex_1_2_dev hδ hβ.ne' mb e p).1 h) t
  simp only at h1 h2
  have he : e (t + 1) - e t = 1 / β * (p t - pbarD α β y rs mb) := by linarith
  have hp : p (t + 1) - p t = θ * (δ * (e t - ebarD δ γ φ α β y g ps rs mb) -
      (δ + γ / β) * (p t - pbarD α β y rs mb)) := by
    simp only [dM11] at h1; linarith
  rw [he, hp]
  constructor
  · rw [mul_nonneg_iff_of_pos_left (one_div_pos.2 hβ), sub_nonneg]
  · rw [mul_nonneg_iff_of_pos_left hθ, sub_nonneg]

theorem pbarD_sub (mb mb' : ℝ) : pbarD α β y rs mb' = pbarD α β y rs mb + (mb' - mb) := by
  simp only [pbarD]; ring

theorem ebarD_sub (mb mb' : ℝ) :
    ebarD δ γ φ α β y g ps rs mb' = ebarD δ γ φ α β y g ps rs mb + (mb' - mb) := by
  simp only [ebarD, pbarD]; ring

/-- The saddle slope of the Dornbusch model is negative: `k < 0`. -/
theorem dK_neg (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) : dK θ δ γ β < 0 := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have := (lamLo_lt_m11 h1 (dorn_hm hδ hθ hβ)).1
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- **Exercise 2(d)** (Miao, p. 43): after an unexpected permanent increase `m̄ → m̄'` at date 0,
starting from the old steady state `p₀ = p̄(m̄)`, the path `p_t = p̄' − λᵗΔm`,
`e_t = ē' − kλᵗΔm` (`Δm = m̄' − m̄`, `λ = λ_lo`) solves the model and converges to the new
steady state. -/
theorem ex_1_2d_path (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) (mb mb' : ℝ) :
    IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb')
        (fun t => ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)))
        (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) ∧
      pbarD α β y rs mb' - dLo θ δ γ β ^ 0 * (mb' - mb) = pbarD α β y rs mb ∧
      Tendsto (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) atTop
        (𝓝 (pbarD α β y rs mb')) ∧
      Tendsto (fun t => ebarD δ γ φ α β y g ps rs mb' -
        dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb))) atTop
        (𝓝 (ebarD δ γ φ α β y g ps rs mb')) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hS := saddle22 h1 (by positivity : θ * δ ≠ 0) (-(mb' - mb))
  have hsol : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb')
      (fun t => ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)))
      (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) := by
    rw [ex_1_2_dev hδ.ne' hβ.ne']
    have e1 : (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb) - pbarD α β y rs mb') =
        fun t => dLo θ δ γ β ^ t * (-(mb' - mb)) := by ext t; ring
    have e2 : (fun t => ebarD δ γ φ α β y g ps rs mb' -
        dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)) - ebarD δ γ φ α β y g ps rs mb') =
        fun t => dLo θ δ γ β ^ t * (dK θ δ γ β * -(mb' - mb)) := by ext t; ring
    rw [e1, e2]
    exact hS
  have hp0 : pbarD α β y rs mb' - dLo θ δ γ β ^ 0 * (mb' - mb) = pbarD α β y rs mb := by
    rw [pbarD_sub mb mb']; ring
  obtain ⟨t1, t2⟩ := dorn_tendsto hδ hθ hβ hcond hsol (by simp only [pow_zero]; ring)
  exact ⟨hsol, hp0, t1, t2⟩

/-- **Exercise 2(d)** (Miao, p. 43): this is the only bounded path from `p₀ = p̄(m̄)`. -/
theorem ex_1_2d_unique (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) {mb mb' : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb') e p) (hp0 : p 0 = pbarD α β y rs mb)
    (hp : BddSeq p) (he : BddSeq e) :
    p = (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) ∧
      e = (fun t => ebarD δ γ φ α β y g ps rs mb' -
        dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb))) := by
  have hk := (ex_1_2b_unique hδ hθ hβ hcond h).1 ⟨hp, he⟩
  obtain ⟨hsol, -, -, -⟩ := ex_1_2d_path (φ := φ) (α := α) (y := y) (g := g) (ps := ps)
    (rs := rs) hδ hθ hβ hcond mb mb'
  have hd := (ex_1_2_dev hδ.ne' hβ.ne' mb' e p).1 h
  have hd' := (ex_1_2_dev hδ.ne' hβ.ne' mb' _ _).1 hsol
  have hP0 : p 0 - pbarD α β y rs mb' = -(mb' - mb) := by rw [hp0, pbarD_sub mb mb']; ring
  obtain ⟨hX, hY⟩ := hd.ext hd' (by simp only [pow_zero]; rw [hP0]; ring)
    (by simp only [pow_zero]; rw [hk, hP0]; ring)
  constructor
  · ext t; have := congrFun hX t; linarith
  · ext t; have := congrFun hY t; linarith

/-- **Exercise 2(d)** (Miao, p. 43), overshooting: for `m̄' > m̄` the exchange rate jumps at date
0 to `e₀ = ē' − kΔm` above its new steady state `ē'`, and depreciates by `(1 − k)Δm > Δm`. -/
theorem ex_1_2d_overshoot (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ}
    (hm : mb < mb') :
    ebarD δ γ φ α β y g ps rs mb' <
        ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ 0 * (mb' - mb)) ∧
      ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ 0 * (mb' - mb)) -
          ebarD δ γ φ α β y g ps rs mb = (1 - dK θ δ γ β) * (mb' - mb) ∧
      mb' - mb < (1 - dK θ δ γ β) * (mb' - mb) := by
  have hk := dK_neg (γ := γ) hδ hθ hβ
  have hΔ : 0 < mb' - mb := by linarith
  refine ⟨?_, by rw [ebarD_sub mb mb']; ring, by nlinarith⟩
  simp only [pow_zero, one_mul]
  nlinarith

/-- **Exercise 2(d)** (Miao, p. 43): if the stable root is positive (`0 < λ < 1`), the price
rises and the exchange rate falls monotonically towards the new steady state. -/
theorem ex_1_2d_monotone (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ}
    (hm : mb < mb') (hl : 0 < dLo θ δ γ β) (t : ℕ) :
    pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb) <
        pbarD α β y rs mb' - dLo θ δ γ β ^ (t + 1) * (mb' - mb) ∧
      ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ (t + 1) * (mb' - mb)) <
        ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)) := by
  have hk := dK_neg (γ := γ) hδ hθ hβ
  have hl1 := (roots22_lt (dorn_h1 (γ := γ) hδ hθ hβ)).1
  have hΔ : 0 < mb' - mb := by linarith
  have hpt := pow_pos hl t
  have hd : 0 < dLo θ δ γ β ^ t * (mb' - mb) * (1 - dLo θ δ γ β) :=
    mul_pos (mul_pos hpt hΔ) (by linarith)
  rw [pow_succ]
  constructor
  · nlinarith
  · nlinarith

/-- One-step dynamics of the announced-increase economy (Exercise 2(e)): before `T` the
deviations from the old steady state move by the matrix, and from `T` on the deviations from the
new steady state solve the 2×2 system. -/
theorem dorn_announce_core (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ} {T : ℕ}
    {e p : ℕ → ℝ} (h : IsDorn2 δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e p) :
    IsSol22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (fun t => p (T + t) - pbarD α β y rs mb')
        (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') ∧
      sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β) (fun t => p (T + t) - pbarD α β y rs mb')
          (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') 0 =
        dHi θ δ γ β ^ T * sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β)
          (fun t => p t - pbarD α β y rs mb) (fun t => e t - ebarD δ γ φ α β y g ps rs mb) 0 -
          (1 / β + dHi θ δ γ β - dM11 θ δ γ β) * (mb' - mb) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hnew : IsSol22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (fun t => p (T + t) - pbarD α β y rs mb')
      (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') := fun t =>
    (ex_1_2_dev_step (m := cagan_money mb mb' T) (t := T + t) (mc := mb') hδ.ne' hβ.ne'
      (by simp only [cagan_money, show ¬ T + t < T by omega, ↓reduceIte])).1 (h (T + t))
  have hold : ∀ k, k ≤ T → sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β)
      (fun t => p t - pbarD α β y rs mb) (fun t => e t - ebarD δ γ φ α β y g ps rs mb) k =
      dHi θ δ γ β ^ k * sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β)
      (fun t => p t - pbarD α β y rs mb) (fun t => e t - ebarD δ γ φ α β y g ps rs mb) 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hstep := (ex_1_2_dev_step (m := cagan_money mb mb' T) (t := n) (mc := mb) hδ.ne'
        hβ.ne'
        (by simp only [cagan_money, show n < T by omega, ↓reduceIte])).1 (h n)
      rw [sVar_step (cp22_lamHi h1) hstep.1 hstep.2, ih (by omega), pow_succ]
      ring
  refine ⟨hnew, ?_⟩
  rw [← hold T le_rfl]
  simp only [sVar, add_zero]
  rw [pbarD_sub mb mb', ebarD_sub mb mb']
  ring

/-- The exchange-rate jump of Exercise 2(e):
`J(T) = λ_hi^{−T}(1 + (1/β)/(λ_hi − m₁₁))Δm`. -/
noncomputable def dornJump (θ δ γ β mb mb' : ℝ) (T : ℕ) : ℝ :=
  (dHi θ δ γ β ^ T)⁻¹ * (1 + 1 / β / (dHi θ δ γ β - dM11 θ δ γ β)) * (mb' - mb)

/-- **Exercise 2(e)** (Miao, p. 43): with the increase to `m̄'` announced for date `T` and the
economy at the old steady state (`p₀ = p̄(m̄)`), every bounded path has the exchange rate jump
`e₀ = ē(m̄) + λ_hi^{−T}(1 + (1/β)/(λ_hi − m₁₁))Δm` at the announcement. -/
theorem ex_1_2e_jump (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ} {T : ℕ}
    {e p : ℕ → ℝ} (h : IsDorn2 δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e p)
    (hp0 : p 0 = pbarD α β y rs mb) (hp : BddSeq p) (he : BddSeq e) :
    e 0 = ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  obtain ⟨hnew, hs⟩ := dorn_announce_core hδ hθ hβ h
  have hpT : BddSeq (fun t => p (T + t)) := by obtain ⟨M, hM⟩ := hp; exact ⟨M, fun t => hM _⟩
  have heT : BddSeq (fun t => e (T + t)) := by obtain ⟨M, hM⟩ := he; exact ⟨M, fun t => hM _⟩
  have hz := sHi_zero_of_bdd h1 hnew (bddSeq_sub_const hpT _) (bddSeq_sub_const heT _)
  rw [hz] at hs
  have hgap : 0 < dHi θ δ γ β - dM11 θ δ γ β := by
    linarith [(lamLo_lt_m11 h1 (dorn_hm hδ hθ hβ)).2]
  have hhi : 0 < dHi θ δ γ β := by linarith [(roots22_lt h1).2]
  have hT : dHi θ δ γ β ^ T ≠ 0 := (pow_pos hhi T).ne'
  simp only [sVar, hp0, sub_self, mul_zero, zero_add] at hs
  have key : e 0 - ebarD δ γ φ α β y g ps rs mb = ((1 / β + (dHi θ δ γ β - dM11 θ δ γ β)) *
      (mb' - mb)) / (dHi θ δ γ β ^ T * (dHi θ δ γ β - dM11 θ δ γ β)) := by
    rw [eq_div_iff (mul_ne_zero hT hgap.ne')]
    linear_combination (-1 : ℝ) * hs
  rw [show e 0 = ebarD δ γ φ α β y g ps rs mb + (e 0 - ebarD δ γ φ α β y g ps rs mb) by ring, key]
  simp only [dornJump]
  field_simp
  ring

/-- **Exercise 2(e)** (Miao, p. 43): the path starting at `p₀ = p̄(m̄)`, `e₀ = ē(m̄) + J(T)`
exists, and (under the stability condition) converges to the new steady state, so it is the
unique bounded path. -/
theorem ex_1_2e_exists (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) (mb mb' : ℝ) (T : ℕ) :
    Tendsto (fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T)
        (ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T) (pbarD α β y rs mb) t).2)
        atTop (𝓝 (pbarD α β y rs mb')) ∧
      Tendsto (fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T)
        (ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T) (pbarD α β y rs mb) t).1)
        atTop (𝓝 (ebarD δ γ φ α β y g ps rs mb')) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hm := dorn_hm hδ hθ hβ
  have hc : 0 < cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (-1) := by
    rw [dorn_cp_neg_one hβ.ne']; linarith
  set e0 := ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T
  set p := fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e0
    (pbarD α β y rs mb) t).2 with hpdef
  set e := fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e0
    (pbarD α β y rs mb) t).1 with hedef
  have hsol : IsDorn2 δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e p := dornIter_sol _ _ _
  obtain ⟨hnew, hs⟩ := dorn_announce_core hδ hθ hβ hsol
  have hgap : 0 < dHi θ δ γ β - dM11 θ δ γ β := by
    linarith [(lamLo_lt_m11 h1 hm).2]
  have hhi : 0 < dHi θ δ γ β := by linarith [(roots22_lt h1).2]
  have hT : dHi θ δ γ β ^ T ≠ 0 := (pow_pos hhi T).ne'
  have hz : sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β) (fun t => p (T + t) - pbarD α β y rs mb')
      (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') 0 = 0 := by
    rw [hs]
    have hp0 : p 0 = pbarD α β y rs mb := rfl
    have he0 : e 0 = e0 := rfl
    simp only [sVar, hp0, he0, e0, dornJump, sub_self, mul_zero, zero_add, add_sub_cancel_left]
    field_simp
    ring
  have hk := (sHi_zero_iff h1 hm _ _ 0).1 hz
  obtain ⟨hX, hY⟩ := hnew.ext (saddle22 h1 (by positivity) (p (T + 0) - pbarD α β y rs mb'))
    (by simp) (by simpa using hk)
  obtain ⟨t1, t2⟩ := saddle22_tendsto h1 hc (p (T + 0) - pbarD α β y rs mb')
  rw [← hX] at t1
  rw [← hY] at t2
  have t1' := t1.add_const (pbarD α β y rs mb')
  have t2' := t2.add_const (ebarD δ γ φ α β y g ps rs mb')
  simp only [sub_add_cancel, zero_add] at t1' t2'
  constructor
  · rw [← tendsto_add_atTop_iff_nat T]
    exact t1'.congr (fun t => by rw [add_comm])
  · rw [← tendsto_add_atTop_iff_nat T]
    exact t2'.congr (fun t => by rw [add_comm])

/-- **Exercise 2(e)** (Miao, p. 43): for `m̄' > m̄` the exchange rate depreciates on the
announcement (`J(T) > 0`), by less the further away the increase (`J(T + 1) < J(T)`), and for
`T = 0` the jump is the overshooting jump `(1 − k)Δm` of part (d). -/
theorem ex_1_2e_jump_shape (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ}
    (hm : mb < mb') (T : ℕ) :
    0 < dornJump θ δ γ β mb mb' T ∧ dornJump θ δ γ β mb mb' (T + 1) < dornJump θ δ γ β mb mb' T ∧
      dornJump θ δ γ β mb mb' 0 = (1 - dK θ δ γ β) * (mb' - mb) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hm12 := dorn_hm hδ hθ hβ
  have hgap : 0 < dHi θ δ γ β - dM11 θ δ γ β := by
    linarith [(lamLo_lt_m11 h1 hm12).2]
  have hhi : 1 < dHi θ δ γ β := (roots22_lt h1).2
  have hΔ : 0 < mb' - mb := by linarith
  have hc : 0 < 1 + 1 / β / (dHi θ δ γ β - dM11 θ δ γ β) := by positivity
  have hpos : ∀ n : ℕ, 0 < (dHi θ δ γ β ^ n)⁻¹ := fun n => inv_pos.2 (pow_pos (by linarith) n)
  refine ⟨mul_pos (mul_pos (hpos T) hc) hΔ, ?_, ?_⟩
  · simp only [dornJump]
    have : (dHi θ δ γ β ^ (T + 1))⁻¹ < (dHi θ δ γ β ^ T)⁻¹ := by
      rw [pow_succ, mul_inv]
      have := hpos T
      have : (dHi θ δ γ β)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hhi
      nlinarith
    have := mul_pos hc hΔ
    nlinarith
  · have hprod : (dLo θ δ γ β - dM11 θ δ γ β) * (dHi θ δ γ β - dM11 θ δ γ β) =
        -(θ * δ * (1 / β)) := by
      have := cp22_factor h1 (dM11 θ δ γ β)
      simp only [cp22] at this
      linarith
    have hm0 : θ * δ ≠ 0 := by positivity
    have hq : 1 / β / (dHi θ δ γ β - dM11 θ δ γ β) = -(dLo θ δ γ β - dM11 θ δ γ β) / (θ * δ) := by
      rw [div_eq_div_iff hgap.ne' hm0]
      linear_combination hprod
    simp only [dornJump, dK, kSaddle, pow_zero, inv_one, one_mul]
    rw [hq]
    ring

end Miao.DifferenceEquations

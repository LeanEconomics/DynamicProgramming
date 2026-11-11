/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMQuantitativeMethods.Cholesky
import RationalExpectations.VARMoments

/-!
# VARs and local projections

AKMM, the box "Defining the fiscal multiplier in a dynamic economy", p. 220; the box "From
natural experiments to impulse response functions: local projection", p. 221; §8.5,
pp. 225–227, with footnote 6.

* **Dynamic multipliers** (box, p. 220): the peak and cumulative multipliers; when the output
  response is proportional to the spending response, `y_h = mG_h` with `m ≥ 0`, both equal `m`
  (`vl_peak_multiplier_prop`, `vl_cum_multiplier_prop`).
* **VAR impulse responses** (p. 226): for `yₜ = A₁yₜ₋₁ + uₜ`, a shock `v` to `uₜ` moves
  `y_{t+h}` by `A₁ʰv`, the identity on impact (`vl_var1_irf`, from Miao's
  `var_impulse_response`); the companion form of a VAR(J) (`vl_companion`, `vl_companion_rec`,
  the book's `J = 2` display `vl_companion_two`) and its impulse responses as the upper-left
  block of `𝒜ʰ` (`vl_companion_irf`).
* **Population estimands** (p. 226). The outcome `Y = y_{t+h}` and the regressor `yₜ` are
  written `Y = Θuₜ + Ψv + Mw`, `yₜ = uₜ + Nw`, with `w` the lags, `v` the later innovations,
  `uₜ ⟂ w`, `v ⟂ w`, `v ⟂ uₜ`, `Σ = E[uₜuₜ']`. The book's "least squares equates with a
  conditional expectation" for Gaussian data is taken in its linear-projection form.
  * The local projection on `y_{1,t}` (controlling for `w`) has coefficients
    `β_i = (ΘΣ)_{i1}/Σ₁₁`, and they exist (`vl_lp_estimand`, `vl_lp_exists`).
  * The VAR projection on `yₜ` has coefficient matrix `Γ` with `ΓΣ = ΘΣ`, so `Γ = Θ` for
    invertible `Σ` (`vl_var_estimand`, `vl_var_exists`); the two differ when the innovations are
    correlated (`vl_lp_differs`).
  * **Plagborg-Møller–Wolf** (footnote 6): `β_i = Σⱼ Γ_{ij}(L_{j1}/L₁₁)` with `L` the Cholesky
    factor of `Σ` (`fn_6`).
  * **The LP box** (p. 221): if `y_{1,t} = zₜ` is uncorrelated with the other innovations, the
    local projection is the impulse response, `β_i = Θ_{i1}` (`vl_lp_exogenous`).
  * For a VAR(1), `Θ = A₁ʰ` and `M = A₁ʰ⁺¹`, so the VAR estimand is `A₁ʰ` and the LP estimand
    is `A₁ʰΣe₁/Σ₁₁` (`vl_var1_estimands`).

Departure: the expectations of p. 226 are Gaussian conditional expectations; here they are the
population linear projections, which coincide with them for Gaussian data (not formalised).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Dynamic multipliers -/

/-- AKMM, p. 220 (Mountford–Uhlig): the cumulative multiplier over horizons `0, …, H`,
`Σ_h y_h / Σ_h G_h`. -/
noncomputable def vl_cumMult (y G : ℕ → ℝ) (H : ℕ) : ℝ :=
  (∑ h ∈ Finset.range (H + 1), y h) / ∑ h ∈ Finset.range (H + 1), G h

/-- AKMM, p. 220 (Blanchard–Perotti): the peak multiplier over horizons `0, …, H`,
`max_h y_h / max_h G_h`. -/
noncomputable def vl_peakMult (y G : ℕ → ℝ) (H : ℕ) : ℝ :=
  (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one y /
    (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one G

/-- AKMM, p. 220: if `y_h = mG_h` and `Σ G_h ≠ 0`, the cumulative multiplier is `m`. -/
theorem vl_cum_multiplier_prop {y G : ℕ → ℝ} {m : ℝ} (H : ℕ) (hy : ∀ h, y h = m * G h)
    (hG : ∑ h ∈ Finset.range (H + 1), G h ≠ 0) : vl_cumMult y G H = m := by
  unfold vl_cumMult
  simp only [hy, ← Finset.mul_sum]
  field_simp

/-- AKMM, p. 220: if `y_h = mG_h` with `m ≥ 0` and the peak spending response is nonzero, the
peak multiplier is `m`. -/
theorem vl_peak_multiplier_prop {y G : ℕ → ℝ} {m : ℝ} (H : ℕ) (hy : ∀ h, y h = m * G h)
    (hm : 0 ≤ m) (hG : (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one G ≠ 0) :
    vl_peakMult y G H = m := by
  unfold vl_peakMult
  have hne : (Finset.range (H + 1)).Nonempty := Finset.nonempty_range_add_one
  obtain ⟨h1, hh1, e1⟩ := Finset.exists_mem_eq_sup' hne G
  obtain ⟨h2, hh2, e2⟩ := Finset.exists_mem_eq_sup' hne y
  have hle1 : G h2 ≤ G h1 := e1 ▸ Finset.le_sup' G hh2
  have hle2 : y h1 ≤ y h2 := e2 ▸ Finset.le_sup' y hh1
  rw [e1] at hG ⊢
  rw [e2]
  have : y h2 = m * G h1 := le_antisymm (by rw [hy]; exact mul_le_mul_of_nonneg_left hle1 hm)
    (by rw [← hy]; exact hle2)
  rw [this]
  field_simp

/-! ### VAR impulse responses and the companion form -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The VAR(1) impulse response** (AKMM, p. 226): for `yₜ₊₁ = A₁yₜ + uₜ₊₁`, if `u'` differs
from `u` only by `v` at date `s + 1` (and `y'₀ = y₀`), then `y'_{s+1+h} − y_{s+1+h} = A₁ʰv`; at
`h = 0` this is `v` itself: the reduced-form shock moves a single variable on impact. -/
theorem vl_var1_irf {A : Matrix n n ℝ} {y y' u u' : ℕ → n → ℝ}
    (hrec : ∀ t, y (t + 1) = A *ᵥ y t + u (t + 1))
    (hrec' : ∀ t, y' (t + 1) = A *ᵥ y' t + u' (t + 1)) (h0 : y' 0 = y 0) (s : ℕ) (v : n → ℝ)
    (hu : ∀ t, u' t = if t = s + 1 then u t + v else u t) :
    (∀ h, y' (s + 1 + h) - y (s + 1 + h) = (A ^ h) *ᵥ v) ∧ y' (s + 1) - y (s + 1) = v := by
  have h1 : ∀ t, y (t + 1) = A *ᵥ y t + (1 : Matrix n n ℝ) *ᵥ u (t + 1) := by
    intro t; rw [one_mulVec]; exact hrec t
  have h2 : ∀ t, y' (t + 1) = A *ᵥ y' t + (1 : Matrix n n ℝ) *ᵥ u' (t + 1) := by
    intro t; rw [one_mulVec]; exact hrec' t
  have := (Miao.RationalExpectations.var_impulse_response h1 h2 h0 s v hu).2
  have hh : ∀ h, y' (s + 1 + h) - y (s + 1 + h) = (A ^ h) *ᵥ v := by
    intro h; rw [this h, Matrix.mul_one]
  refine ⟨hh, ?_⟩
  simpa using hh 0

/-- AKMM, p. 226: the companion matrix of a VAR with `m + 1` lags, on the stacked state
`(yₜ, yₜ₋₁, …, yₜ₋ₘ)` indexed by `Fin (m+1) × n`: the first block row is `(A₁, …, A_{m+1})`,
below it identity blocks shift the lags. -/
def vl_companion {m : ℕ} (A : Fin (m + 1) → Matrix n n ℝ) :
    Matrix (Fin (m + 1) × n) (Fin (m + 1) × n) ℝ :=
  Matrix.of fun p q => if p.1 = 0 then A q.1 p.2 q.2 else
    if (q.1 : ℕ) + 1 = p.1 ∧ p.2 = q.2 then 1 else 0

/-- The stacked state `(y_{t+m}, …, y_t)`: block `r` is `y_{t+m−r}`. -/
def vl_stack {m : ℕ} (y : ℕ → n → ℝ) (t : ℕ) : Fin (m + 1) × n → ℝ :=
  fun p => y (t + m - p.1) p.2

/-- The loading of the innovation on the first block. -/
def vl_load (m : ℕ) : Matrix (Fin (m + 1) × n) n ℝ :=
  Matrix.of fun p k => if p.1 = 0 ∧ p.2 = k then 1 else 0

/-- **The companion form** (AKMM, p. 226): if
`y_{t+m+1} = Σ_{c ≤ m} A_{c+1}y_{t+m−c} + u_{t+m+1}` for all `t`, the stacked state is a
first-order system `xₜ₊₁ = 𝒜xₜ + (u_{t+m+1}, 0, …, 0)`. -/
theorem vl_companion_rec {m : ℕ} {A : Fin (m + 1) → Matrix n n ℝ} {y u : ℕ → n → ℝ}
    (hrec : ∀ t, y (t + m + 1) = ∑ c : Fin (m + 1), A c *ᵥ y (t + m - c) + u (t + m + 1))
    (t : ℕ) :
    vl_stack (m := m) y (t + 1) = vl_companion A *ᵥ vl_stack y t + vl_load m *ᵥ u (t + m + 1) := by
  funext p
  obtain ⟨r, i⟩ := p
  simp only [vl_stack, vl_companion, vl_load, mulVec, dotProduct, of_apply, Pi.add_apply,
    Fintype.sum_prod_type]
  by_cases hr : r = 0
  · subst hr
    simp only [↓reduceIte, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, Fin.val_zero, Nat.sub_zero]
    rw [show t + 1 + m = t + m + 1 by ring, hrec t]
    simp only [Pi.add_apply, Finset.sum_apply, mulVec, dotProduct]
  · simp only [hr, ↓reduceIte, false_and, zero_mul, Finset.sum_const_zero, add_zero]
    obtain ⟨r', hr'⟩ : ∃ r' : Fin (m + 1), (r' : ℕ) + 1 = r := by
      refine ⟨⟨(r : ℕ) - 1, by omega⟩, ?_⟩
      have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
      simp only; omega
    rw [Finset.sum_eq_single r']
    · simp only [hr', true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      congr 1
      omega
    · intro c _ hc
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ¬ ((c : ℕ) + 1 = r) := fun h => hc (Fin.ext (by omega))
      simp [this]
    · simp

omit [Fintype n] in
/-- **The `J = 2` companion matrix** (AKMM, p. 226): `𝒜 = [[A₁, A₂], [I, 0]]`, entrywise. -/
theorem vl_companion_two (A : Fin 2 → Matrix n n ℝ) (i k : n) :
    vl_companion A (0, i) (0, k) = A 0 i k ∧ vl_companion A (0, i) (1, k) = A 1 i k ∧
      vl_companion A (1, i) (0, k) = (1 : Matrix n n ℝ) i k ∧
      vl_companion A (1, i) (1, k) = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [vl_companion, one_apply]
  · simp [vl_companion]

/-- **Impulse responses of a VAR(J)** (AKMM, p. 226): if two solutions of the VAR with `m + 1`
lags have the same initial values `y₀, …, y_m` and their innovations differ only by `v` at date
`s + m + 1`, then `y'_{s+m+1+h} − y_{s+m+1+h} = Σ_k (𝒜ʰ)_{(0,i),(0,k)}v_k`: the IRFs are the
upper-left `n × n` block of `𝒜ʰ`, which is the identity at `h = 0`. -/
theorem vl_companion_irf {m : ℕ} {A : Fin (m + 1) → Matrix n n ℝ} {y y' u u' : ℕ → n → ℝ}
    (hrec : ∀ t, y (t + m + 1) = ∑ c : Fin (m + 1), A c *ᵥ y (t + m - c) + u (t + m + 1))
    (hrec' : ∀ t, y' (t + m + 1) = ∑ c : Fin (m + 1), A c *ᵥ y' (t + m - c) + u' (t + m + 1))
    (h0 : ∀ r ≤ m, y' r = y r) (s : ℕ) (v : n → ℝ)
    (hu : ∀ t, u' t = if t = s + m + 1 then u t + v else u t) (h : ℕ) (i : n) :
    y' (s + m + 1 + h) i - y (s + m + 1 + h) i =
      ∑ k, (vl_companion A ^ h) (0, i) (0, k) * v k := by
  have e1 : ∀ t, vl_stack (m := m) y (t + 1) =
      vl_companion A *ᵥ vl_stack y t + vl_load m *ᵥ (fun t => u (t + m)) (t + 1) := by
    intro t; beta_reduce; rw [vl_companion_rec hrec t, show t + 1 + m = t + m + 1 by ring]
  have e2 : ∀ t, vl_stack (m := m) y' (t + 1) =
      vl_companion A *ᵥ vl_stack y' t + vl_load m *ᵥ (fun t => u' (t + m)) (t + 1) := by
    intro t; beta_reduce; rw [vl_companion_rec hrec' t, show t + 1 + m = t + m + 1 by ring]
  have hst0 : vl_stack (m := m) y' 0 = vl_stack y 0 := by
    funext p; simp only [vl_stack]; exact congrFun (h0 _ (by omega)) _
  have hshock : ∀ t, (fun t => u' (t + m)) t =
      if t = s + 1 then (fun t => u (t + m)) t + v else (fun t => u (t + m)) t := by
    intro t
    simp only
    rw [hu]
    by_cases ht : t = s + 1
    · subst ht; simp [show s + 1 + m = s + m + 1 by ring]
    · have : t + m ≠ s + m + 1 := by omega
      simp [ht, this]
  have := (Miao.RationalExpectations.var_impulse_response e1 e2 hst0 s v hshock).2 h
  have hc := congrFun this (0, i)
  simp only [vl_stack, Pi.sub_apply, Fin.val_zero, Nat.sub_zero] at hc
  rw [show s + 1 + h + m = s + m + 1 + h by ring] at hc
  rw [hc, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single (0, k)]
  · simp [vl_load]
  · intro q _ hq
    have : ¬ (q.1 = 0 ∧ q.2 = k) := fun hh => hq (Prod.ext hh.1 hh.2)
    simp [vl_load, this]
  · simp

/-! ### Population estimands of local projections and VARs -/

/-- The coefficient matrix that puts `β` on the regressor `y_{1,t}` (column `i₁`) and zero on
the others. -/
def vl_col (β : n → ℝ) (i1 : n) : Matrix n n ℝ := Matrix.of fun i k => if k = i1 then β i else 0

variable {J K : Type*} [Fintype J] [Fintype K]

omit [DecidableEq n] in
/-- The second moments of a projection residual `e = Y − Byₜ − aw`, with
`Y = Θuₜ + Ψv + Mw` and `yₜ = uₜ + Nw`: `E[euₜ'] = ΘΣ − BΣ`, `E[ew'] = (M − BN − a)E[ww']` and
`E[eyₜ'] = E[euₜ'] + E[ew']N'`. -/
theorem vl_mom_resid {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M : Matrix n J ℝ)
    (N : Matrix n J ℝ) (B : Matrix n n ℝ) (a : Matrix n J ℝ) :
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) u = Θ * var_mom μ u u - B * var_mom μ u u ∧
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) w = (M - B * N - a) * var_mom μ w w ∧
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) (u + kf_app N w) =
        var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
          kf_app a w) u +
        var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
          kf_app a w) w * Nᵀ := by
  have hwu : var_mom μ w u = 0 := by rw [kf_mom_transpose, huw, transpose_zero]
  have hyt : kf_L2 μ (u + kf_app N w) := kf_L2_add hu (kf_L2_app hw N)
  have hY : kf_L2 μ (kf_app Θ u + kf_app Ψ v + kf_app M w) :=
    kf_L2_add (kf_L2_add (kf_L2_app hu Θ) (kf_L2_app hv Ψ)) (kf_L2_app hw M)
  have hBy : kf_L2 μ (kf_app B (u + kf_app N w)) := kf_L2_app hyt B
  have he1 : kf_L2 μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w)) :=
    kf_L2_sub hY hBy
  have hmomu : ∀ {z : Ω → n → ℝ}, kf_L2 μ z →
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) z = Θ * var_mom μ u z + Ψ * var_mom μ v z + M * var_mom μ w z -
          B * (var_mom μ u z + N * var_mom μ w z) - a * var_mom μ w z := by
    intro z hz
    rw [kf_mom_sub_left he1 (kf_L2_app hw a) hz, kf_mom_sub_left hY hBy hz,
      kf_mom_add_left (kf_L2_add (kf_L2_app hu Θ) (kf_L2_app hv Ψ)) (kf_L2_app hw M) hz,
      kf_mom_add_left (kf_L2_app hu Θ) (kf_L2_app hv Ψ) hz, kf_mom_app_left hu hz,
      kf_mom_app_left hv hz, kf_mom_app_left hw hz, kf_mom_app_left hyt hz,
      kf_mom_add_left hu (kf_L2_app hw N) hz, kf_mom_app_left hw hz, kf_mom_app_left hw hz]
  have hmomw : ∀ {z : Ω → J → ℝ}, kf_L2 μ z →
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) z = Θ * var_mom μ u z + Ψ * var_mom μ v z + M * var_mom μ w z -
          B * (var_mom μ u z + N * var_mom μ w z) - a * var_mom μ w z := by
    intro z hz
    rw [kf_mom_sub_left he1 (kf_L2_app hw a) hz, kf_mom_sub_left hY hBy hz,
      kf_mom_add_left (kf_L2_add (kf_L2_app hu Θ) (kf_L2_app hv Ψ)) (kf_L2_app hw M) hz,
      kf_mom_add_left (kf_L2_app hu Θ) (kf_L2_app hv Ψ) hz, kf_mom_app_left hu hz,
      kf_mom_app_left hv hz, kf_mom_app_left hw hz, kf_mom_app_left hyt hz,
      kf_mom_add_left hu (kf_L2_app hw N) hz, kf_mom_app_left hw hz, kf_mom_app_left hw hz]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmomu hu, hvu, hwu]; simp
  · rw [hmomw hw, huw, hvw]; simp only [Matrix.mul_zero, zero_add, add_zero]
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc]
  · rw [kf_mom_add_right hu (kf_L2_app hw N) (kf_L2_sub he1 (kf_L2_app hw a)),
      kf_mom_app_right hw (kf_L2_sub he1 (kf_L2_app hw a))]

/-- **The local-projection estimand** (AKMM, p. 226): if `β, a` are population least-squares
coefficients of the regression of `Y = y_{t+h}` on `y_{1,t}` and the lags `w` (the residual is
orthogonal to `y_{1,t}` and to `w`) and `Σ₁₁ ≠ 0`, then `β_i = (ΘΣ)_{i1}/Σ₁₁`. -/
theorem vl_lp_estimand {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (h11 : var_mom μ u u i1 i1 ≠ 0) (β : n → ℝ) (a : Matrix n J ℝ)
    (horth1 : ∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0) (i : n) :
    β i = (Θ * var_mom μ u u) i i1 / var_mom μ u u i1 i1 := by
  obtain ⟨h1, -, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N (vl_col β i1) a
  rw [h3, horthw, Matrix.zero_mul, add_zero, h1] at horth1
  have := horth1 i
  rw [Matrix.sub_apply, Matrix.mul_apply (M := vl_col β i1)] at this
  simp only [vl_col, of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at this
  field_simp
  linarith

/-- The local projection exists (AKMM, p. 226): `β_i = (ΘΣ)_{i1}/Σ₁₁`, `a = M − (βe₁')N` give a
residual orthogonal to `y_{1,t}` and to `w`. -/
theorem vl_lp_exists {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (h11 : var_mom μ u u i1 i1 ≠ 0) :
    let β : n → ℝ := fun i => (Θ * var_mom μ u u) i i1 / var_mom μ u u i1 i1
    let a := M - vl_col β i1 * N
    (∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0) ∧
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0 := by
  intro β a
  obtain ⟨h1, h2, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N (vl_col β i1) a
  have hw0 : (M - vl_col β i1 * N - a) = 0 := by simp only [a]; abel
  rw [hw0, Matrix.zero_mul] at h2
  refine ⟨fun i => ?_, h2⟩
  rw [h3, h2, Matrix.zero_mul, add_zero, h1, Matrix.sub_apply, Matrix.mul_apply (M := vl_col β i1)]
  simp only [vl_col, of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, β]
  field_simp
  ring

/-- **The VAR estimand** (AKMM, p. 226): if `Γ, a` are population least-squares coefficients of
the regression of `Y` on all of `yₜ` and the lags `w`, then `ΓΣ = ΘΣ`; so `Γ = Θ` when `Σ` is
invertible: the VAR measures the response to `uₜ = e₁` with `y_{j,t}`, `j ≥ 2`, held at zero. -/
theorem vl_var_estimand {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (Γ : Matrix n n ℝ) (a : Matrix n J ℝ)
    (horth : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a w) (u + kf_app N w) = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a w) w = 0) :
    Γ * var_mom μ u u = Θ * var_mom μ u u ∧ (IsUnit (var_mom μ u u).det → Γ = Θ) := by
  obtain ⟨h1, -, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N Γ a
  rw [h3, horthw, Matrix.zero_mul, add_zero, h1] at horth
  have hΓ : Γ * var_mom μ u u = Θ * var_mom μ u u := (sub_eq_zero.1 horth).symm
  refine ⟨hΓ, fun hdet => ?_⟩
  have := congrArg (· * (var_mom μ u u)⁻¹) hΓ
  simpa [Matrix.mul_assoc, mul_nonsing_inv _ hdet] using this

omit [DecidableEq n] in
/-- The VAR projection exists (AKMM, p. 226): `Γ = Θ`, `a = M − ΘN`. -/
theorem vl_var_exists {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ) :
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Θ (u + kf_app N w) -
      kf_app (M - Θ * N) w) (u + kf_app N w) = 0 ∧
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Θ (u + kf_app N w) -
      kf_app (M - Θ * N) w) w = 0 := by
  obtain ⟨h1, h2, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N Θ (M - Θ * N)
  have hw0 : (M - Θ * N - (M - Θ * N)) = 0 := sub_self _
  rw [hw0, Matrix.zero_mul] at h2
  refine ⟨?_, h2⟩
  rw [h3, h2, Matrix.zero_mul, add_zero, h1, sub_self]

/-- **Footnote 6** (Plagborg-Møller and Wolf 2021; AKMM, p. 227): the local projection is a
combination of the VAR impulse responses. If `β` is the LP estimand and `Γ` the VAR estimand,
`Σ = LL'` with `L` lower triangular (`L₁₁ ≠ 0`) and `i₁` the first variable, then
`β_i = Σⱼ Γ_{ij} wⱼ` with weights `wⱼ = L_{j1}/L₁₁` (so `w₁ = 1`), summed over the `n`
variables. -/
theorem fn_6 [LinearOrder n] {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (hmin : ∀ j, i1 ≤ j) {L : Matrix n n ℝ} (hL : L.IsLowerTriangular)
    (hLS : var_mom μ u u = L * Lᵀ) (hL11 : L i1 i1 ≠ 0) (β : n → ℝ) (a : Matrix n J ℝ)
    (horth1 : ∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0)
    (Γ : Matrix n n ℝ) (a' : Matrix n J ℝ)
    (horth' : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a' w) (u + kf_app N w) = 0)
    (horthw' : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a' w) w = 0) (i : n) :
    β i = ∑ j, Γ i j * (L j i1 / L i1 i1) ∧ L i1 i1 / L i1 i1 = 1 := by
  have h11 : var_mom μ u u i1 i1 ≠ 0 := by
    rw [(ch_first_column hL hLS i1 hmin i1).2.1]; exact pow_ne_zero 2 hL11
  have hβ := vl_lp_estimand hu hv hw huw hvw hvu Θ Ψ M N i1 h11 β a horth1 horthw i
  have hΓ := (vl_var_estimand hu hv hw huw hvw hvu Θ Ψ M N Γ a' horth' horthw').1
  refine ⟨?_, div_self hL11⟩
  rw [hβ, ← hΓ, Matrix.mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc, (ch_first_column hL hLS i1 hmin j).2.2]

/-- **The LP box** (AKMM, p. 221): if the shock of interest `y_{1,t} = z_t` is uncorrelated with
the other innovations (`Σ_{j1} = 0` for `j ≠ 1`), the local projection of `y_{i,t+h}` on `z_t`
is the impulse response `Θ_{i1}`. -/
theorem vl_lp_exogenous {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (h11 : var_mom μ u u i1 i1 ≠ 0) (hexo : ∀ j, j ≠ i1 → var_mom μ u u j i1 = 0)
    (β : n → ℝ) (a : Matrix n J ℝ)
    (horth1 : ∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0) (i : n) :
    β i = Θ i i1 := by
  rw [vl_lp_estimand hu hv hw huw hvw hvu Θ Ψ M N i1 h11 β a horth1 horthw i, Matrix.mul_apply,
    Finset.sum_eq_single i1 (fun j _ hj => by rw [hexo j hj, mul_zero]) (by simp)]
  field_simp

/-- **The VAR(1) estimands** (AKMM, p. 226): for `y_{s+1} = Ay_s + u_{s+1}`, the outcome
`y_{t+1+h}` and the regressor `y_{t+1}` have the representation of `vl_mom_resid` with
`Θ = Aʰ`, `M = Aʰ⁺¹`, `N = A`, `w = y_t` and `v` the innovations `u_{t+1+h−k}`, `k < h`:
`y_{t+1+h} = Aʰu_{t+1} + Σ_{k<h} Aᵏu_{t+1+h−k} + Aʰ⁺¹y_t` and `y_{t+1} = u_{t+1} + Ay_t`. -/
theorem vl_var1_estimands {A : Matrix n n ℝ} {y u : ℕ → Ω → n → ℝ}
    (hrec : ∀ s ω, y (s + 1) ω = A *ᵥ y s ω + u (s + 1) ω) (t h : ℕ) :
    y (t + 1 + h) = kf_app (A ^ h) (u (t + 1)) +
        kf_app (Matrix.of fun r (q : Fin h × n) => (A ^ (q.1 : ℕ)) r q.2)
          (fun ω (q : Fin h × n) => u (t + 1 + h - q.1) ω q.2) +
        kf_app (A ^ (h + 1)) (y t) ∧
      y (t + 1) = u (t + 1) + kf_app A (y t) := by
  refine ⟨?_, ?_⟩
  · funext ω
    have hr : ∀ s, (fun s => y s ω) (s + 1) = A *ᵥ (fun s => y s ω) s +
        (1 : Matrix n n ℝ) *ᵥ (fun s => u s ω) (s + 1) := by
      intro s; rw [one_mulVec]; exact hrec s ω
    have hma := Miao.RationalExpectations.var_ma_shift (x := fun s => y s ω)
      (e := fun s => u s ω) (Φ := A) (Sg := 1) hr (t + 1) h
    simp only [Matrix.mul_one] at hma
    rw [hma, hrec t ω]
    simp only [kf_app, Pi.add_apply, mulVec_add, mulVec_mulVec, ← pow_succ]
    funext r
    simp only [Pi.add_apply, mulVec, dotProduct, of_apply, Fintype.sum_prod_type,
      Finset.sum_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ k, (A ^ i) r k * u (t + 1 + h - i) ω k) h]
    ring
  · funext ω
    rw [hrec t ω]
    simp only [kf_app, Pi.add_apply]
    rw [add_comm]

/-- **The two estimands differ** (AKMM, p. 226: "these two estimation techniques as described
above are estimating different things"): with `Θ = I` and correlated innovations
`Σ = [[1, 1/2], [1/2, 1]]`, the LP coefficient of `y₂` on `y₁` is `(ΘΣ)₂₁/Σ₁₁ = 1/2`, while the
VAR response `Θ₂₁` is `0`. -/
theorem vl_lp_differs :
    let S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * S) 1 0 / S 0 0 = 1 / 2 ∧
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  intro S
  constructor
  · simp [S]
  · simp

end AKMM.QuantitativeMethods

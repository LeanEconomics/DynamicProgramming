/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CDEuler

/-!
# Deterministic income, Case 1 (`βR < 1`): critical levels and the optimal plans

Miao, §8.3.1, Case 1, pp. 240–245. Income is constant, `y_t = y > rb`; write `w = y − rb`
(`x*_{−1}` in the book). The book constructs critical levels `x*_0 < x*_1 < …` and maps
`h_t : [x*_{t−1}, x*_t] → [x*_t, x*_{t+1}]` by backward induction on the Euler equation. We
parametrise the same construction by the cash on hand `z ∈ [w, x*_0]` of the first period in
which the borrowing limit is exhausted:

* `cd1_Params.phi`: `φ(c) = (u′)⁻¹(βRu′(c))`, consumption one period before `c` along the Euler
  equation; `φ(c) > c`, `φ` strictly increasing and continuous.
* `cd1_Params.X k z`: cash on hand `k` periods before the borrowing limit binds at cash `z`:
  `X_0(z) = z`, `X_{k+1}(z) = φ^{k+1}(z) + (X_k(z) − w)/R`. The book's `h_k` is `X_{k+1} ∘ X_k⁻¹`
  and `x*_k = X_k(x*_0) = X_{k+1}(w)` (`cd1_Params.xstar`, `cd1_Params.X_succ_w`).
* `eq_8_10`: `x*_0` is the unique `x > w` with `u′(x) = βRu′(w)`.
* `eq_8_12`, `eq_8_13`: the Euler equations defining `h_0` and `h_t`.
* `cd1_Params.xstar_strictMono` (`x*_{t+1} > x*_t`, p. 244) and `cd1_Params.xstar_tendsto`
  (`x*_t → ∞`, needed for the construction to cover `[w, ∞)` and not proved in the book).
* `cd1_Params.exists_kz`: every `x ≥ w` is `X_k(z)` for some `k` and `z ∈ [w, x*_0]`.
* `cd1_Params.plan_optimal`: the plan `c_t = φ^{k−t}(z)` (`t ≤ k`), `c_t = w` (`t > k`) is
  feasible, satisfies (8.7) and the transversality condition, hence is optimal (`eq_8_14`).
* `eq_8_11`, `cd1_Params.V0_value`: for `x ∈ [w, x*_0]` exhaust the limit at once; the value is
  `u(x) + β/(1−β) u(w)`.
* `cd1_Params.plan_binding`, `cd1_Params.plan_dynamics`: the borrowing limit is not exhausted in
  periods `0, …, k − 1` and is exhausted from `k` on; consumption, cash on hand and saving fall
  until `k` and are then constant (`c_t = x_t = y − rb`, `a_{t+1} = −b`).
-/

namespace Miao.Applications

open Filter Topology

/-- The parameters of §8.3.1, Case 1: utility `U`, `0 < β`, `R > 1`, `βR < 1`, constant income
`y > rb`. -/
structure cd1_Params where
  /-- Utility. -/
  U : cd_Utility
  /-- Discount factor. -/
  β : ℝ
  /-- Gross interest rate. -/
  R : ℝ
  /-- Borrowing limit. -/
  b : ℝ
  /-- Constant labour income. -/
  y : ℝ
  hβ : 0 < β
  hR : 1 < R
  hβR : β * R < 1
  hy : (R - 1) * b < y

namespace cd1_Params

variable (P : cd1_Params)

/-- Net income `w = y − rb` (the book's `x*_{−1}`). -/
def w : ℝ := P.y - (P.R - 1) * P.b

theorem w_pos : 0 < P.w := by unfold w; linarith [P.hy]

theorem R_pos : 0 < P.R := by linarith [P.hR]

theorem βR_pos : 0 < P.β * P.R := mul_pos P.hβ P.R_pos

theorem β_lt_one : P.β < 1 := by
  have := P.hβR
  have := P.hβ
  nlinarith [P.hR]

/-- `φ(c) = (u′)⁻¹(βRu′(c))`: consumption one period earlier along the Euler equation. -/
noncomputable def phi (c : ℝ) : ℝ := P.U.cd_duInv (P.β * P.R * P.U.du c)

theorem phi_pos (c : ℝ) : 0 < P.phi c := P.U.cd_duInv_pos _

theorem du_phi {c : ℝ} (hc : 0 < c) : P.U.du (P.phi c) = P.β * P.R * P.U.du c :=
  P.U.cd_du_duInv (mul_pos P.βR_pos (P.U.du_pos c hc))

/-- `φ(c) > c` since `βR < 1`. -/
theorem lt_phi {c : ℝ} (hc : 0 < c) : c < P.phi c := by
  by_contra hle
  push Not at hle
  have h1 : P.U.du c ≤ P.U.du (P.phi c) := by
    rcases hle.lt_or_eq with h | h
    · exact (P.U.du_anti (Set.mem_Ioi.2 (P.phi_pos c)) (Set.mem_Ioi.2 hc) h).le
    · rw [h]
  rw [P.du_phi hc] at h1
  have := P.U.du_pos c hc
  nlinarith [P.hβR]

theorem phi_strictMono : StrictMonoOn P.phi (Set.Ioi 0) := by
  intro c hc c' hc' h
  have h1 := P.U.du_anti hc hc' h
  refine P.U.cd_duInv_anti (Set.mem_Ioi.2 (mul_pos P.βR_pos (P.U.du_pos _ hc')))
    (Set.mem_Ioi.2 (mul_pos P.βR_pos (P.U.du_pos _ hc))) ?_
  exact mul_lt_mul_of_pos_left h1 P.βR_pos

theorem phi_cont : ContinuousOn P.phi (Set.Ioi 0) := by
  refine P.U.cd_duInv_cont.comp (P.U.du_cont.const_smul (P.β * P.R)) fun c hc => ?_
  exact Set.mem_Ioi.2 (mul_pos P.βR_pos (P.U.du_pos c hc))

theorem phi_mapsTo : Set.MapsTo P.phi (Set.Ioi 0) (Set.Ioi 0) := fun c _ => P.phi_pos c

theorem iter_pos {z : ℝ} (hz : 0 < z) (k : ℕ) : 0 < P.phi^[k] z := by
  induction k with
  | zero => exact hz
  | succ k _ => rw [Function.iterate_succ_apply']; exact P.phi_pos _

theorem iter_lt_succ {z : ℝ} (hz : 0 < z) (k : ℕ) : P.phi^[k] z < P.phi^[k + 1] z := by
  rw [Function.iterate_succ_apply']
  exact P.lt_phi (P.iter_pos hz k)

theorem le_iter {z : ℝ} (hz : 0 < z) (k : ℕ) : z ≤ P.phi^[k] z := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (P.iter_lt_succ hz k).le

theorem iter_strictMono (k : ℕ) : StrictMonoOn P.phi^[k] (Set.Ioi 0) := by
  induction k with
  | zero => exact strictMono_id.strictMonoOn _
  | succ k ih =>
    intro a ha b hb hab
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact P.phi_strictMono (P.phi_mapsTo.iterate k ha) (P.phi_mapsTo.iterate k hb) (ih ha hb hab)

theorem iter_cont (k : ℕ) : ContinuousOn P.phi^[k] (Set.Ioi 0) :=
  P.phi_cont.iterate P.phi_mapsTo k

theorem du_iter {z : ℝ} (hz : 0 < z) (k : ℕ) :
    P.U.du (P.phi^[k] z) = (P.β * P.R) ^ k * P.U.du z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', P.du_phi (P.iter_pos hz k), ih, pow_succ]
    ring

/-- `φᵏ(z)` is unbounded: `u′(φᵏ(z)) = (βR)ᵏu′(z) → 0`. -/
theorem iter_unbounded {z : ℝ} (hz : 0 < z) (M : ℝ) : ∃ k, M < P.phi^[k] z := by
  by_contra hall
  push Not at hall
  set M' := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : ∀ k, P.U.du M' ≤ P.U.du (P.phi^[k] z) := fun k => by
    have h1 : P.phi^[k] z ≤ M' := (hall k).trans (le_max_left _ _)
    rcases h1.lt_or_eq with h | h
    · exact (P.U.du_anti (Set.mem_Ioi.2 (P.iter_pos hz k)) (Set.mem_Ioi.2 hM') h).le
    · rw [h]
  have hlim : Tendsto (fun k : ℕ => (P.β * P.R) ^ k * P.U.du z) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one P.βR_pos.le P.hβR).mul_const (P.U.du z)
    simpa using this
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (P.U.du_pos M' hM'))).exists
  have := hle k
  rw [P.du_iter hz] at this
  linarith

/-- Cash on hand `k` periods before the borrowing limit binds at cash `z`:
`X_0(z) = z`, `X_{k+1}(z) = φ^{k+1}(z) + (X_k(z) − w)/R`. -/
noncomputable def X : ℕ → ℝ → ℝ
  | 0, z => z
  | k + 1, z => P.phi^[k + 1] z + (X k z - P.w) / P.R

theorem X_zero (z : ℝ) : P.X 0 z = z := rfl

theorem X_succ (k : ℕ) (z : ℝ) : P.X (k + 1) z = P.phi^[k + 1] z + (P.X k z - P.w) / P.R :=
  rfl

theorem w_le_X {z : ℝ} (hz : P.w ≤ z) (k : ℕ) : P.w ≤ P.X k z := by
  have hz0 : 0 < z := lt_of_lt_of_le P.w_pos hz
  induction k with
  | zero => exact hz
  | succ k ih =>
    rw [X_succ]
    have h1 := P.le_iter hz0 (k + 1)
    have h2 : 0 ≤ (P.X k z - P.w) / P.R := div_nonneg (sub_nonneg.2 ih) P.R_pos.le
    linarith

theorem X_lt_succ {z : ℝ} (hz : P.w ≤ z) (k : ℕ) : P.X k z < P.X (k + 1) z := by
  have hz0 : 0 < z := lt_of_lt_of_le P.w_pos hz
  induction k with
  | zero =>
    rw [X_succ, X_zero, Function.iterate_one]
    have h1 := P.lt_phi hz0
    have h2 : 0 ≤ (z - P.w) / P.R := div_nonneg (sub_nonneg.2 hz) P.R_pos.le
    linarith
  | succ k ih =>
    rw [X_succ P k.succ, X_succ P k]
    have h1 := P.iter_lt_succ hz0 (k + 1)
    have h2 : (P.X k z - P.w) / P.R < (P.X (k + 1) z - P.w) / P.R :=
      div_lt_div_of_pos_right (by linarith) P.R_pos
    rw [X_succ] at h2
    linarith

theorem X_strictMono (k : ℕ) : StrictMonoOn (P.X k) (Set.Ioi 0) := by
  induction k with
  | zero => exact strictMono_id.strictMonoOn _
  | succ k ih =>
    intro a ha b hb hab
    rw [X_succ, X_succ]
    have h1 := P.iter_strictMono (k + 1) ha hb hab
    have h2 : (P.X k a - P.w) / P.R < (P.X k b - P.w) / P.R :=
      div_lt_div_of_pos_right (by linarith [ih ha hb hab]) P.R_pos
    linarith

theorem X_cont (k : ℕ) : ContinuousOn (P.X k) (Set.Ioi 0) := by
  induction k with
  | zero => exact continuousOn_id
  | succ k ih =>
    have : P.X (k + 1) = fun z => P.phi^[k + 1] z + (P.X k z - P.w) / P.R :=
      funext fun z => P.X_succ k z
    rw [this]
    exact (P.iter_cont (k + 1)).add ((ih.sub continuousOn_const).div_const _)

theorem iter_le_X {z : ℝ} (hz : P.w ≤ z) (k : ℕ) : P.phi^[k] z ≤ P.X k z := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    rw [X_succ]
    have : 0 ≤ (P.X k z - P.w) / P.R :=
      div_nonneg (sub_nonneg.2 (P.w_le_X hz k)) P.R_pos.le
    linarith

/-- Miao, (8.10), p. 241: `x*_0 = φ(w)`, the cash on hand at which `u′(x*_0) = βRu′(y − rb)`. -/
noncomputable def xstar0 : ℝ := P.phi P.w

/-- Miao, p. 241–245: the critical level `x*_k = X_{k+1}(w)` (`x*_{−1} = w`, `x*_0 = φ(w)`). -/
noncomputable def xstar (k : ℕ) : ℝ := P.X (k + 1) P.w

theorem xstar_zero : P.xstar 0 = P.xstar0 := by
  simp [xstar, xstar0, X_succ, X_zero]

/-- The two descriptions of the critical points agree: `X_{k+1}(w) = X_k(x*_0)`, so the plans
of the intervals `[x*_{k−1}, x*_k]` and `[x*_k, x*_{k+1}]` coincide at `x*_k` (the book's
`h_k(x*_k) = h_{k+1}(x*_k)`, `V_k(x*_k) = V_{k+1}(x*_k)`). -/
theorem X_succ_w (k : ℕ) : P.X (k + 1) P.w = P.X k P.xstar0 := by
  induction k with
  | zero => simp [X_succ, X_zero, xstar0]
  | succ k ih =>
    rw [X_succ, ih]
    cases k with
    | zero => simp [X_succ, X_zero, xstar0, Function.iterate_succ_apply]
    | succ k =>
      rw [X_succ P (k + 1) P.xstar0, xstar0, Function.iterate_succ_apply]

theorem xstar_eq (k : ℕ) : P.xstar k = P.X k P.xstar0 := P.X_succ_w k

/-- Miao, (8.10), p. 241: `x*_0` is the unique `x > y − rb` with `u′(x) = βRu′(y − rb)`. -/
theorem eq_8_10 : P.w < P.xstar0 ∧ P.U.du P.xstar0 = P.β * P.R * P.U.du P.w ∧
    ∀ x, P.w < x → P.U.du x = P.β * P.R * P.U.du P.w → x = P.xstar0 := by
  refine ⟨P.lt_phi P.w_pos, P.du_phi P.w_pos, fun x hx hdu => ?_⟩
  refine P.U.cd_du_inj (lt_trans P.w_pos hx) (P.phi_pos _) ?_
  rw [hdu, xstar0, P.du_phi P.w_pos]

/-- Miao, p. 244: `x*_{t+1} > x*_t` (and `x*_0 > x*_{−1} = w`). -/
theorem xstar_strictMono : StrictMono P.xstar :=
  strictMono_nat_of_lt_succ fun k => P.X_lt_succ le_rfl (k + 1)

theorem w_lt_xstar (k : ℕ) : P.w < P.xstar k := by
  rw [P.xstar_eq]
  exact lt_of_lt_of_le (P.eq_8_10.1) (by
    have := P.le_iter (P.phi_pos P.w) k
    exact le_trans (P.le_iter (P.phi_pos P.w) 0) (le_trans this
      (P.iter_le_X (P.eq_8_10.1.le) k)))

/-- The critical levels go to infinity, so the intervals `[x*_{t−1}, x*_t]` cover `[y − rb, ∞)`
(used in the book's "By induction, we can define … on the whole state space"). -/
theorem xstar_tendsto : Tendsto P.xstar atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone P.xstar_strictMono.monotone fun M => ?_
  obtain ⟨k, hk⟩ := P.iter_unbounded (P.phi_pos P.w) M
  refine ⟨k, hk.le.trans ?_⟩
  rw [P.xstar_eq]
  exact P.iter_le_X P.eq_8_10.1.le k

/-- Miao, (8.12), p. 242: `h_0(z)` solves `u′(x − (z − y + rb)/R) = βRu′(z) = βRV_0′(z)`:
`u′(X_1(z) − (z − w)/R) = βRu′(z)`. -/
theorem eq_8_12 {z : ℝ} (hz : P.w ≤ z) :
    P.U.du (P.X 1 z - (z - P.w) / P.R) = P.β * P.R * P.U.du z := by
  rw [X_succ, X_zero, add_sub_cancel_right, Function.iterate_one]
  exact P.du_phi (lt_of_lt_of_le P.w_pos hz)

/-- Miao, (8.13), p. 244: `h_t` solves the Euler equation between periods `0` and `1`:
`u′(X_{k+2}(z) − (X_{k+1}(z) − w)/R) = βRu′(X_{k+1}(z) − (X_k(z) − w)/R)`. -/
theorem eq_8_13 {z : ℝ} (hz : P.w ≤ z) (k : ℕ) :
    P.U.du (P.X (k + 2) z - (P.X (k + 1) z - P.w) / P.R) =
      P.β * P.R * P.U.du (P.X (k + 1) z - (P.X k z - P.w) / P.R) := by
  rw [X_succ P (k + 1), X_succ P k, add_sub_cancel_right, add_sub_cancel_right,
    Function.iterate_succ_apply' _ (k + 1)]
  exact P.du_phi (P.iter_pos (lt_of_lt_of_le P.w_pos hz) _)

/-- Every `x ≥ y − rb` is `X_k(z)` for some `k` and `z ∈ [w, x*_0]`. -/
theorem exists_kz {x : ℝ} (hx : P.w ≤ x) :
    ∃ k z, P.w ≤ z ∧ z ≤ P.xstar0 ∧ P.X k z = x := by
  have hex : ∃ k, x ≤ P.X k P.xstar0 := by
    obtain ⟨k, hk⟩ := (P.xstar_tendsto.eventually_ge_atTop x).exists
    exact ⟨k, by rwa [← P.xstar_eq]⟩
  classical
  set k := Nat.find hex
  have hk : x ≤ P.X k P.xstar0 := Nat.find_spec hex
  have hlow : P.X k P.w ≤ x := by
    cases hk' : k with
    | zero => simpa [X_zero] using hx
    | succ j =>
      have := Nat.find_min hex (show j < k by omega)
      push Not at this
      rw [X_succ_w]
      exact this.le
  have hcont : ContinuousOn (P.X k) (Set.Icc P.w P.xstar0) :=
    (P.X_cont k).mono fun z hz => Set.mem_Ioi.2 (lt_of_lt_of_le P.w_pos hz.1)
  obtain ⟨z, hz, hzx⟩ := intermediate_value_Icc P.eq_8_10.1.le hcont ⟨hlow, hk⟩
  exact ⟨k, z, hz.1, hz.2, hzx⟩

/-- The plan that exhausts the borrowing limit from period `k` on at cash `z`: consumption. -/
noncomputable def pc (k : ℕ) (z : ℝ) (t : ℕ) : ℝ := if t ≤ k then P.phi^[k - t] z else P.w

/-- The plan that exhausts the borrowing limit from period `k` on at cash `z`: cash on hand. -/
noncomputable def px (k : ℕ) (z : ℝ) (t : ℕ) : ℝ := if t ≤ k then P.X (k - t) z else P.w

/-- The constant income sequence. -/
def ys : ℕ → ℝ := fun _ => P.y

theorem plan_feasible (k : ℕ) {z : ℝ} (hz : P.w ≤ z) :
    cd_Feasible P.R P.b P.ys (P.X k z) (P.pc k z) (P.px k z) := by
  have hz0 : 0 < z := lt_of_lt_of_le P.w_pos hz
  refine ⟨⟨by simp [px], fun t => ?_⟩, fun t => ?_⟩
  · simp only [px, pc, ys]
    by_cases ht : t + 1 ≤ k
    · have ht' : t ≤ k := by omega
      simp only [ht, ht', ↓reduceIte]
      obtain ⟨j, hj⟩ : ∃ j, k - t = j + 1 := ⟨k - t - 1, by omega⟩
      rw [hj, show k - (t + 1) = j by omega, X_succ]
      have := P.R_pos
      field_simp
      unfold w
      ring
    · simp only [ht, ↓reduceIte]
      by_cases ht' : t ≤ k
      · simp only [ht', ↓reduceIte]
        rw [show k - t = 0 by omega, X_zero, Function.iterate_zero, id, sub_self, mul_zero,
          zero_add]
        rfl
      · simp only [ht', ↓reduceIte, sub_self, mul_zero, zero_add]
        rfl
  · simp only [pc, px]
    split_ifs
    · exact ⟨P.iter_pos hz0 _, P.iter_le_X hz _⟩
    · exact ⟨P.w_pos, le_rfl⟩

theorem plan_saving (k : ℕ) (z : ℝ) (t : ℕ) :
    P.px k z t - P.pc k z t = if t < k then (P.X (k - t - 1) z - P.w) / P.R else 0 := by
  simp only [px, pc]
  by_cases ht : t < k
  · have ht' : t ≤ k := ht.le
    simp only [ht, ht', ↓reduceIte]
    obtain ⟨j, hj⟩ : ∃ j, k - t = j + 1 := ⟨k - t - 1, by omega⟩
    rw [hj, show j + 1 - 1 = j by omega, X_succ]
    ring
  · simp only [ht, ↓reduceIte]
    by_cases ht' : t ≤ k
    · simp only [ht', ↓reduceIte]
      rw [show k - t = 0 by omega]
      simp [X_zero]
    · simp only [ht', ↓reduceIte, sub_self]

theorem plan_euler (k : ℕ) {z : ℝ} (hz : P.w ≤ z) (hz' : z ≤ P.xstar0) :
    cd_Euler P.U P.β P.R (P.pc k z) (P.px k z) := by
  have hz0 : 0 < z := lt_of_lt_of_le P.w_pos hz
  intro t
  by_cases ht : t < k
  · have e : P.pc k z t = P.phi (P.pc k z (t + 1)) := by
      simp only [pc, ht.le, show t + 1 ≤ k by omega, ↓reduceIte]
      rw [show k - t = (k - (t + 1)) + 1 by omega, Function.iterate_succ_apply']
    have hpos : 0 < P.pc k z (t + 1) := ((P.plan_feasible k hz).2 (t + 1)).1
    rw [e, P.du_phi hpos]
    exact ⟨le_rfl, fun _ => rfl⟩
  · have hs : ¬ P.pc k z t < P.px k z t := by
      have := P.plan_saving k z t
      simp only [ht, ↓reduceIte] at this
      linarith
    refine ⟨?_, fun h => absurd h hs⟩
    have e1 : P.pc k z (t + 1) = P.w := by simp [pc, show ¬ t + 1 ≤ k by omega]
    rw [e1]
    by_cases htk : t = k
    · have e2 : P.pc k z t = z := by simp [pc, htk]
      rw [e2, ← P.du_phi P.w_pos]
      rcases hz'.lt_or_eq with h | h
      · exact (P.U.du_anti (Set.mem_Ioi.2 hz0) (Set.mem_Ioi.2 (P.phi_pos _)) h).le
      · rw [h, xstar0]
    · have e2 : P.pc k z t = P.w := by simp [pc, show ¬ t ≤ k by omega]
      rw [e2]
      have := P.U.du_pos _ P.w_pos
      nlinarith [P.hβR]

theorem plan_tvcs (k : ℕ) (z : ℝ) : cd_TVCs P.U P.β (P.pc k z) (P.px k z) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop k] with t ht
  rw [P.plan_saving k z t]
  simp [show ¬ t < k by omega]

/-- Miao, (8.14), pp. 244–245: for `x = X_k(z)`, `z ∈ [w, x*_0]` (i.e. `x ∈ [x*_{k−1}, x*_k]`),
the plan consuming `φ^{k−t}(z)` until `k` and `y − rb` afterwards is optimal: it is feasible,
satisfies the Euler inequality (8.7) and the transversality condition. -/
theorem eq_8_14 (k : ℕ) {z : ℝ} (hz : P.w ≤ z) (hz' : z ≤ P.xstar0) :
    cd_Optimal P.U P.β P.R P.b P.ys (P.X k z) (P.pc k z) (P.px k z) :=
  cd_sufficient P.U P.hβ.le (P.plan_feasible k hz) (P.plan_euler k hz hz') (P.plan_tvcs k z)

/-- Miao, (8.11), p. 241: for `x ∈ [y − rb, x*_0]` the plan `c_0 = x`, `c_t = y − rb` (`t ≥ 1`),
`a_{t+1} = −b`, is optimal. -/
theorem eq_8_11 {x : ℝ} (hx : P.w ≤ x) (hx' : x ≤ P.xstar0) :
    cd_Optimal P.U P.β P.R P.b P.ys x (fun t => if t = 0 then x else P.w)
      (fun t => if t = 0 then x else P.w) := by
  have e1 : P.pc 0 x = fun t => if t = 0 then x else P.w := funext fun t => by
    simp [pc]
  have e2 : P.px 0 x = fun t => if t = 0 then x else P.w := funext fun t => by
    simp [px, X_zero]
  have := P.eq_8_14 0 hx hx'
  rwa [e1, e2, X_zero] at this

/-- Miao, pp. 244–245: for `z > w` (i.e. `x ∈ (x*_{k−1}, x*_k]`) the consumer does not exhaust
the borrowing limit in periods `0, …, k − 1` (`â_{t+1} > 0`) and exhausts it from period `k` on;
from period `k + 1` on `c_t = x_t = y − rb`. -/
theorem plan_binding (k : ℕ) {z : ℝ} (hz : P.w < z) :
    (∀ t < k, P.pc k z t < P.px k z t) ∧ (∀ t, k ≤ t → P.pc k z t = P.px k z t) ∧
      ∀ t, k < t → P.pc k z t = P.w ∧ P.px k z t = P.w := by
  have hz0 : 0 < z := lt_trans P.w_pos hz
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := P.plan_saving k z t
    simp only [ht, ↓reduceIte] at this
    have h1 : z ≤ P.X (k - t - 1) z :=
      (P.le_iter hz0 _).trans (P.iter_le_X hz.le _)
    have h2 : 0 < (P.X (k - t - 1) z - P.w) / P.R := div_pos (by linarith) P.R_pos
    linarith
  · have := P.plan_saving k z t
    simp only [show ¬ t < k by omega, ↓reduceIte] at this
    linarith
  · simp [pc, px, show ¬ t ≤ k by omega]

/-- Miao, p. 245: "there is a finite time `T` such that consumption `c_t`, savings `a_{t+1}`, and
cash on hand `x_t` all decrease until period `T`, and after period `T` they are constant": all
three are nonincreasing, consumption and cash strictly decrease before `k`. -/
theorem plan_dynamics (k : ℕ) {z : ℝ} (hz : P.w ≤ z) :
    Antitone (P.pc k z) ∧ Antitone (P.px k z) ∧ Antitone (fun t => P.px k z t - P.pc k z t) ∧
      ∀ t < k, P.pc k z (t + 1) < P.pc k z t ∧ P.px k z (t + 1) < P.px k z t := by
  have hz0 : 0 < z := lt_of_lt_of_le P.w_pos hz
  have hstrict : ∀ t < k, P.pc k z (t + 1) < P.pc k z t ∧ P.px k z (t + 1) < P.px k z t := by
    intro t ht
    obtain ⟨j, hj⟩ : ∃ j, k - t = j + 1 := ⟨k - t - 1, by omega⟩
    simp only [pc, px, ht.le, show t + 1 ≤ k by omega, ↓reduceIte, hj,
      show k - (t + 1) = j by omega]
    exact ⟨P.iter_lt_succ hz0 j, P.X_lt_succ hz j⟩
  refine ⟨antitone_nat_of_succ_le fun t => ?_, antitone_nat_of_succ_le fun t => ?_,
    antitone_nat_of_succ_le fun t => ?_, hstrict⟩
  · by_cases ht : t < k
    · exact (hstrict t ht).1.le
    · by_cases htk : t = k
      · subst htk; simp [pc, hz]
      · simp [pc, show ¬ t ≤ k by omega, show ¬ t + 1 ≤ k by omega]
  · by_cases ht : t < k
    · exact (hstrict t ht).2.le
    · by_cases htk : t = k
      · subst htk; simp [px, X_zero, hz]
      · simp [px, show ¬ t ≤ k by omega, show ¬ t + 1 ≤ k by omega]
  · simp only [P.plan_saving]
    by_cases ht : t + 1 < k
    · simp only [ht, show t < k by omega, ↓reduceIte]
      refine div_le_div_of_nonneg_right ?_ P.R_pos.le
      have := P.X_lt_succ hz (k - (t + 1) - 1)
      rw [show k - (t + 1) - 1 + 1 = k - t - 1 by omega] at this
      linarith
    · simp only [ht, ↓reduceIte]
      split_ifs
      · exact div_nonneg (sub_nonneg.2 (P.w_le_X hz _)) P.R_pos.le
      · exact le_rfl

theorem plan_eventually (k : ℕ) (z : ℝ) : ∀ t, k < t → P.pc k z t = P.w := fun t ht => by
  simp [pc, show ¬ t ≤ k by omega]

/-- A plan that is eventually `w` has summable utility. -/
theorem summable_of_eventually {c : ℕ → ℝ} (K : ℕ) (hc : ∀ t, K ≤ t → c t = P.w) :
    Summable fun t => P.β ^ t * P.U.u (c t) := by
  refine (summable_nat_add_iff K).1 ?_
  have : (fun t => P.β ^ (t + K) * P.U.u (c (t + K))) =
      fun t => (P.β ^ K * P.U.u P.w) * P.β ^ t := funext fun t => by
    rw [hc (t + K) (Nat.le_add_left _ _), pow_add]; ring
  rw [this]
  exact (summable_geometric_of_lt_one P.hβ.le P.β_lt_one).mul_left _

theorem plan_summable (k : ℕ) (z : ℝ) : Summable fun t => P.β ^ t * P.U.u (P.pc k z t) :=
  P.summable_of_eventually (k + 1) fun t ht => P.plan_eventually k z t (by omega)

/-- Miao, p. 245: the value of the plan of `eq_8_14`:
`∑_{t≤k} βᵗu(φ^{k−t}(z)) + β^{k+1}u(y − rb)/(1 − β)`. -/
theorem plan_value (k : ℕ) (z : ℝ) :
    ∑' t, P.β ^ t * P.U.u (P.pc k z t) =
      ∑ t ∈ Finset.range (k + 1), P.β ^ t * P.U.u (P.phi^[k - t] z) +
        P.β ^ (k + 1) / (1 - P.β) * P.U.u P.w := by
  rw [← (P.plan_summable k z).sum_add_tsum_nat_add (k + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    simp [pc, show t ≤ k by have := Finset.mem_range.1 ht; omega]
  · have : (fun t => P.β ^ (t + (k + 1)) * P.U.u (P.pc k z (t + (k + 1)))) =
        fun t => (P.β ^ (k + 1) * P.U.u P.w) * P.β ^ t := funext fun t => by
      rw [P.plan_eventually k z _ (by omega), pow_add]; ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one P.hβ.le P.β_lt_one]
    field_simp

/-- Miao, p. 242: `V_0(x) = u(x) + β/(1−β) u(y − rb)` for `x ∈ [x*_{−1}, x*_0]`, the value of
the plan (8.11). -/
theorem V0_value (x : ℝ) :
    ∑' t, P.β ^ t * P.U.u (if t = 0 then x else P.w) =
      P.U.u x + P.β / (1 - P.β) * P.U.u P.w := by
  have e1 : P.pc 0 x = fun t => if t = 0 then x else P.w := funext fun t => by
    simp [pc]
  have := P.plan_value 0 x
  rw [e1] at this
  rw [this]
  simp

end cd1_Params

end Miao.Applications

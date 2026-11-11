/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXAdjustment
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Algebra.Monoid

/-!
# Proposition 14.3.1 (Exercise 14.4): marginal Q equals average Q

Miao, §14.3.3, pp. 498–499, and Exercise 14.4, p. 508, on the event tree of `RXTree`. A
variable chosen at a node `h` (date `t`) is `K_{t+1} = Kn h`; at a successor `g = s :: h` the
capital in place is `Kn g.tail`, the firm hires `N g`, invests `I g` and pays the dividend
`D g = z g F(Kn g.tail, N g) − w g N g − I g` (`rx_div`). The firm discounts with the
household's stochastic discount factor `m g = βΛ_g/Λ_{g.tail}` (`rx_sdf`).

* **Proposition 14.3.1**: if `F` and `Φ` are linearly homogeneous, then under (14.42), (14.48),
  (14.49), `w = zF_N` and the transversality condition `Eₜ[M_{t,t+n}Q_{t+n}K_{t+n+1}] → 0`,
  `QₜK_{t+1} = Pₜ`, the ex-dividend value `Pₜ = Σ_{j ≥ 1} Eₜ[M_{t,t+j}D_{t+j}]`, so
  `Qₜ = Pₜ/K_{t+1}` (`proposition_14_3_1`; the one-step identity is `rx_hayashi_step`).
  This `Pₜ` satisfies the book's definition `Pₜ = Eₜ[βΛ_{t+1}V_{t+1}/Λₜ]` with
  `V_{t+1} = D_{t+1} + P_{t+1}` (`rx_P_recursion`).
* `Qₜ = ∂Pₜ/∂K_{t+1}`: the firm's value `W(k)` (the supremum over plans feasible from `k` of a
  positively homogeneous valuation of their dividends, `rx_firmValue`) is homogeneous of degree
  one (`rx_firmValue_homog`, by scaling plans, `rx_scale_feasible`, `rx_div_scale`); so is
  `P(k) = Eₜ[m W(k)]`, whose derivative is therefore `P/K = Q` (`proposition_14_3_1_marginal`).
  A concrete valuation: the truncated present value (`rx_truncValue_homog`).
* The stock return equals the investment return,
  `R_{s,t+1} = (P_{t+1} + D_{t+1})/Pₜ = (Q_{t+1}(1 − δ + Φ_K) + R_{k,t+1})/Qₜ`
  (`rx_stock_return`), using `D = R_kK − I` (`rx_dividend_eq`). The book's displayed chain
  drops `K_{t+1}` from `R_{k,t+1}` in its second line (a misprint; the result is right).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- The firm's dividend at a non-root node `g`: `D = zF(K, N) − wN − I`, with `K = Kn g.tail`
the capital chosen at the parent node. -/
def rx_div {S : Type*} (F : ℝ × ℝ → ℝ) (z w N I Kn : List S → ℝ) (g : List S) : ℝ :=
  z g * F (Kn g.tail, N g) - w g * N g - I g

/-- The household's stochastic discount factor `m g = βΛ_g/Λ_{g.tail}`. -/
noncomputable def rx_sdf {S : Type*} (β : ℝ) (Λ : List S → ℝ) (g : List S) : ℝ :=
  β * Λ g / Λ g.tail

/-- The one-step identity behind Proposition 14.3.1 (Miao, p. 498): with `F`, `Φ` linearly
homogeneous, `w = zF_N`, `QΦ_I = 1` and (14.42),
`D_{t+1} + Q_{t+1}K_{t+2} = K_{t+1}(z_{t+1}F_K + Q_{t+1}(1 − δ + Φ_K))`. -/
theorem rx_hayashi_step {Φ F : ℝ × ℝ → ℝ} {δ z w N I K1 K2 Q a b FK FN : ℝ}
    (hΦhom : ∀ l : ℝ, 0 < l → Φ (l * I, l * K1) = l * Φ (I, K1))
    (hFhom : ∀ l : ℝ, 0 < l → F (l * K1, l * N) = l * F (K1, N))
    (hΦd : rx_HasPartials Φ a b (I, K1)) (hFd : rx_HasPartials F FK FN (K1, N))
    (hacc : K2 = (1 - δ) * K1 + Φ (I, K1)) (h48 : Q * a = 1) (hw : w = z * FN) :
    z * F (K1, N) - w * N - I + Q * K2 = K1 * (z * FK + Q * (1 - δ + b)) := by
  rw [hacc, rx_euler_homog hFhom hFd, rx_euler_homog hΦhom hΦd, hw]
  linear_combination I * h48

/-- **Proposition 14.3.1** (Miao, p. 498) = **Exercise 14.4** (p. 508). If `F` and `Φ` are
linearly homogeneous, `Λ > 0`, and the plan satisfies (14.42), (14.48), (14.49), `w = zF_N`,
and the transversality condition at `h`, then `QₕK_{t+1} = Pₕ`, where `Pₕ` is the ex-dividend
value of the firm, the limit of `Σ_{j<n} Eₜ[M_{t,t+j+1}D_{t+j+1}]`; hence `Qₕ = Pₕ/K_{t+1}`
(marginal Q equals average Q). -/
theorem proposition_14_3_1 {S : Type*} [Fintype S] (T : RXTree S) {Φ F : ℝ × ℝ → ℝ}
    {δ β : ℝ} {Kn I N z w Λ Q a b FK FN P : List S → ℝ}
    (hΦhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p)
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p)
    (hΦd : ∀ h s, rx_HasPartials Φ (a (s :: h)) (b (s :: h)) (I (s :: h), Kn h))
    (hFd : ∀ h s, rx_HasPartials F (FK (s :: h)) (FN (s :: h)) (Kn h, N (s :: h)))
    (hacc : ∀ h s, Kn (s :: h) = (1 - δ) * Kn h + Φ (I (s :: h), Kn h))
    (h48 : ∀ h s, Q (s :: h) * a (s :: h) = 1)
    (hw : ∀ h s, w (s :: h) = z (s :: h) * FN (s :: h))
    (h49 : ∀ h, Λ h * Q h = β * rx_E T (fun g => Λ g * (z g * FK g + Q g * (1 - δ + b g))) h)
    (hΛ : ∀ h, 0 < Λ h) (h : List S)
    (hP : Tendsto (fun n => ∑ j ∈ Finset.range n,
      rx_pv T (rx_sdf β Λ) (j + 1) (rx_div F z w N I Kn) h) atTop (𝓝 (P h)))
    (htvc : Tendsto (fun n => rx_pv T (rx_sdf β Λ) n (fun g => Q g * Kn g) h) atTop (𝓝 0)) :
    Q h * Kn h = P h ∧ (0 < Kn h → Q h = P h / Kn h) := by
  have hrec : ∀ h', Q h' * Kn h' = rx_E T (fun g => rx_sdf β Λ g *
      (rx_div F z w N I Kn g + Q g * Kn g)) h' := by
    intro h'
    have hs : ∀ s, rx_sdf β Λ (s :: h') * (rx_div F z w N I Kn (s :: h') + Q (s :: h') *
        Kn (s :: h')) = Kn h' / Λ h' * (β * (Λ (s :: h') * (z (s :: h') * FK (s :: h') +
          Q (s :: h') * (1 - δ + b (s :: h'))))) := by
      intro s
      have e := rx_hayashi_step (fun l hl => hΦhom l (I (s :: h'), Kn h') hl)
        (fun l hl => hFhom l (Kn h', N (s :: h')) hl) (hΦd h' s) (hFd h' s) (hacc h' s)
        (h48 h' s) (hw h' s)
      simp only [rx_div, rx_sdf, List.tail_cons]
      rw [e]
      field_simp
    simp only [rx_E]
    rw [Finset.sum_congr rfl fun s _ => by rw [hs s]]
    have : ∑ s, T.cp h' s * (Kn h' / Λ h' * (β * (Λ (s :: h') * (z (s :: h') * FK (s :: h') +
        Q (s :: h') * (1 - δ + b (s :: h')))))) = Kn h' / Λ h' * (β * rx_E T (fun g => Λ g *
          (z g * FK g + Q g * (1 - δ + b g))) h') := by
      simp only [rx_E, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, ← h49 h']
    have := hΛ h'
    field_simp
  have hlim := rx_pv_limit T hrec h htvc
  have heq : Q h * Kn h = P h := tendsto_nhds_unique hlim hP
  exact ⟨heq, fun hK => by rw [← heq]; field_simp⟩

/-- Miao, p. 498: the ex-dividend value defined as the present value of future dividends
satisfies the book's definition `Pₜ = Eₜ[βΛ_{t+1}V_{t+1}/Λₜ]` with the cum-dividend value
`V_{t+1} = D_{t+1} + P_{t+1}`. -/
theorem rx_P_recursion {S : Type*} [Fintype S] (T : RXTree S) {m d P : List S → ℝ}
    (hP : ∀ h, Tendsto (fun n => ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d h) atTop (𝓝 (P h)))
    (h : List S) : P h = rx_E T (fun g => m g * (d g + P g)) h := by
  have h1 : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), rx_pv T m (j + 1) d h) atTop
      (𝓝 (P h)) := (hP h).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), rx_pv T m (j + 1) d h) atTop
      (𝓝 (rx_E T (fun g => m g * (d g + P g)) h)) := by
    have e : ∀ n, ∑ j ∈ Finset.range (n + 1), rx_pv T m (j + 1) d h =
        ∑ s, T.cp h s * (m (s :: h) * (d (s :: h) +
          ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d (s :: h))) := by
      intro n
      rw [Finset.sum_range_succ', rx_pv_sum,
        show rx_pv T m (0 + 1) d h = ∑ s, T.cp h s * (m (s :: h) * d (s :: h)) from rfl,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [e, rx_E]
    refine tendsto_finsetSum _ fun s _ => ?_
    exact ((tendsto_const_nhds.add (hP (s :: h))).const_mul _).const_mul _
  exact tendsto_nhds_unique h1 h2

/-- Miao, p. 499: `D_{t+1} = R_{k,t+1}K_{t+1} − I_{t+1}` when `F` is linearly homogeneous and
`R_k = zF_K`, `w = zF_N`. -/
theorem rx_dividend_eq {F : ℝ × ℝ → ℝ} {z w R N I K FK FN : ℝ}
    (hFhom : ∀ l : ℝ, 0 < l → F (l * K, l * N) = l * F (K, N))
    (hFd : rx_HasPartials F FK FN (K, N)) (hR : R = z * FK) (hw : w = z * FN) :
    z * F (K, N) - w * N - I = R * K - I := by
  rw [rx_euler_homog hFhom hFd, hR, hw]
  ring

/-- Miao, pp. 498–499: the stock return equals the investment return. With `Pₜ = QₜK_{t+1}`,
`P_{t+1} = Q_{t+1}K_{t+2}` (Proposition 14.3.1), `D_{t+1} = R_{k,t+1}K_{t+1} − I_{t+1}`,
(14.42), Euler's identity `Φ = Φ_I I + Φ_K K` and `Q_{t+1}Φ_I = 1`:
`(P_{t+1} + D_{t+1})/Pₜ = (Q_{t+1}(1 − δ + Φ_K) + R_{k,t+1})/Qₜ`. -/
theorem rx_stock_return {δ P P' D' Q Q' K1 K2 R' I' Φv a' b' : ℝ} (hP : P = Q * K1)
    (hP' : P' = Q' * K2) (hD : D' = R' * K1 - I') (hK2 : K2 = (1 - δ) * K1 + Φv)
    (hΦ : Φv = I' * a' + K1 * b') (hQ' : Q' * a' = 1) (hQ : Q ≠ 0) (hK1 : K1 ≠ 0) :
    (P' + D') / P = (Q' * (1 - δ + b') + R') / Q := by
  rw [hP, hP', hD, hK2, hΦ]
  have : Q' * ((1 - δ) * K1 + (I' * a' + K1 * b')) + (R' * K1 - I') =
      K1 * (Q' * (1 - δ + b') + R') := by linear_combination I' * hQ'
  rw [this]
  field_simp

/-- The plans feasible for the firm from initial capital `k`: `p = (I, K, N)` with `K` the
capital in place at each node, `K_root = k` and (14.42). -/
def rx_firmFeasible {S : Type*} (δ : ℝ) (Φ : ℝ × ℝ → ℝ) (k : ℝ) :
    Set ((List S → ℝ) × (List S → ℝ) × (List S → ℝ)) :=
  {p | p.2.1 [] = k ∧ ∀ h s, p.2.1 (s :: h) = (1 - δ) * p.2.1 h + Φ (p.1 h, p.2.1 h)}

/-- The dividends of a plan `p = (I, K, N)`. -/
def rx_divPlan {S : Type*} (F : ℝ × ℝ → ℝ) (z w : List S → ℝ)
    (p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)) (g : List S) : ℝ :=
  z g * F (p.2.1 g, p.2.2 g) - w g * p.2.2 g - p.1 g

/-- The firm's value from capital `k`: the supremum, over feasible plans, of a valuation `val`
of their dividends. -/
noncomputable def rx_firmValue {S : Type*} (val : (List S → ℝ) → ℝ) (δ : ℝ)
    (Φ F : ℝ × ℝ → ℝ) (z w : List S → ℝ) (k : ℝ) : ℝ :=
  sSup ((fun p => val (rx_divPlan F z w p)) '' rx_firmFeasible δ Φ k)

/-- Scaling a plan: `(λI, λK, λN)`. -/
def rx_scale {S : Type*} (l : ℝ) (p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)) :
    (List S → ℝ) × (List S → ℝ) × (List S → ℝ) :=
  (fun g => l * p.1 g, fun g => l * p.2.1 g, fun g => l * p.2.2 g)

/-- With `Φ` linearly homogeneous, a plan feasible from `k` scales to a plan feasible from
`λk`. -/
theorem rx_scale_feasible {S : Type*} {δ : ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΦhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p) {l k : ℝ}
    (hl : 0 < l) {p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)}
    (hp : p ∈ rx_firmFeasible δ Φ k) : rx_scale l p ∈ rx_firmFeasible δ Φ (l * k) := by
  refine ⟨by simp [rx_scale, hp.1], fun h s => ?_⟩
  simp only [rx_scale]
  rw [hp.2 h s, hΦhom l (p.1 h, p.2.1 h) hl]
  ring

/-- With `F` linearly homogeneous, the dividends of the scaled plan are `λ` times the
dividends. -/
theorem rx_div_scale {S : Type*} {F : ℝ × ℝ → ℝ} {z w : List S → ℝ}
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p) {l : ℝ}
    (hl : 0 < l) (p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)) :
    rx_divPlan F z w (rx_scale l p) = fun g => l * rx_divPlan F z w p g := by
  funext g
  simp only [rx_divPlan, rx_scale]
  rw [hFhom l (p.2.1 g, p.2.2 g) hl]
  ring

open Pointwise in
/-- Miao, p. 498 (Proposition 14.3.1, `∂Pₜ/∂K_{t+1}`): with `F`, `Φ` linearly homogeneous and a
positively homogeneous valuation, the firm's value is homogeneous of degree one in capital. -/
theorem rx_firmValue_homog {S : Type*} {val : (List S → ℝ) → ℝ} {δ : ℝ} {Φ F : ℝ × ℝ → ℝ}
    {z w : List S → ℝ}
    (hval : ∀ (l : ℝ) (D : List S → ℝ), 0 < l → val (fun g => l * D g) = l * val D)
    (hΦhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p)
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p) {l k : ℝ}
    (hl : 0 < l) : rx_firmValue val δ Φ F z w (l * k) = l * rx_firmValue val δ Φ F z w k := by
  unfold rx_firmValue
  have hset : (fun p => val (rx_divPlan F z w p)) '' rx_firmFeasible δ Φ (l * k) =
      l • ((fun p => val (rx_divPlan F z w p)) '' rx_firmFeasible δ Φ k) := by
    ext x
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨val (rx_divPlan F z w (rx_scale l⁻¹ p)), ⟨rx_scale l⁻¹ p, ?_, rfl⟩, ?_⟩
      · have := rx_scale_feasible hΦhom (inv_pos.2 hl) hp
        rwa [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      · rw [rx_div_scale hFhom (inv_pos.2 hl), hval _ _ (inv_pos.2 hl), ← mul_assoc,
          mul_inv_cancel₀ hl.ne', one_mul]
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨rx_scale l p, rx_scale_feasible hΦhom hl hp,
        by rw [rx_div_scale hFhom hl, hval _ _ hl]⟩
  rw [hset, Real.sSup_smul_of_nonneg hl.le, smul_eq_mul]

/-- `rx_pv` is linear in the payoff. -/
theorem rx_pv_smul {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (n : ℕ) (l : ℝ)
    (x : List S → ℝ) (h : List S) : rx_pv T m n (fun g => l * x g) h = l * rx_pv T m n x h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [rx_pv, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- A concrete positively homogeneous valuation: the present value of dividends over the first
`N` periods, `Σ_{j<N} E₀[M_{0,j}D_j]`. -/
theorem rx_truncValue_homog {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (N : ℕ)
    (l : ℝ) (D : List S → ℝ) :
    ∑ j ∈ Finset.range N, rx_pv T m j (fun g => l * D g) [] =
      l * ∑ j ∈ Finset.range N, rx_pv T m j D [] := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => rx_pv_smul T m j l D []

/-- **Proposition 14.3.1** (Miao, p. 498), `Qₜ = ∂Pₜ/∂K_{t+1}`. Let the ex-dividend value as a
function of `K_{t+1} = k` be `P(k) = Eₜ[m_{t+1}W_{t+1}(k)]`, each continuation value
`W_{t+1}(s)` homogeneous of degree one (`rx_firmValue_homog`). Then `P` is homogeneous of
degree one, and if `P(K_{t+1}) = QₜK_{t+1}` (`proposition_14_3_1`) with `K_{t+1} > 0`, then
`P′(K_{t+1}) = Qₜ`. -/
theorem proposition_14_3_1_marginal {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {m : S → ℝ} {W : S → ℝ → ℝ} (hW : ∀ s (l k : ℝ), 0 < l → W s (l * k) = l * W s k)
    {Q K1 : ℝ} (hK1 : 0 < K1) (hPQ : rx_Es T h (fun s => m s * W s K1) = Q * K1) :
    (∀ l k : ℝ, 0 < l → rx_Es T h (fun s => m s * W s (l * k)) =
      l * rx_Es T h (fun s => m s * W s k)) ∧
    HasDerivAt (fun k => rx_Es T h (fun s => m s * W s k)) Q K1 := by
  have hhom : ∀ l k : ℝ, 0 < l → rx_Es T h (fun s => m s * W s (l * k)) =
      l * rx_Es T h (fun s => m s * W s k) := by
    intro l k hl
    rw [← rx_Es_mul_left]
    congr 1
    funext s
    rw [hW s l k hl]
    ring
  refine ⟨hhom, ?_⟩
  have := rx_homog_hasDerivAt (P := fun k => rx_Es T h (fun s => m s * W s k))
    (fun l k hl _ => hhom l k hl) hK1
  simp only [hPQ] at this
  rwa [mul_div_cancel_right₀ Q hK1.ne'] at this

end Miao.NeoclassicalGrowth

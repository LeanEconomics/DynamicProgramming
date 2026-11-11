/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AAVariational

/-!
# Recursive divergence utility

Miao, §20.2.2, pp. 696–697: belief distortions as a martingale (20.8) and the recursive divergence
utility, on a finite event tree with one-step-ahead reference distributions `p h` and a finite
horizon (`U_T = u(c_T)`).

* A one-step density `m_{t+1} = π̂(s_{t+1}|s_t)/π(s_{t+1}|s_t)` at the node `h` is a nonnegative
  `m : S → ℝ` with `E_t m = 1` (`aa_Admissible`); the distortion `M_{t+1} = m_{t+1}M_t`, `M₀ = 1`
  (20.8) (`aa_M`) is a martingale (`aa_M_martingale`).
* `R_t(x) = min_m E_t[m x + θ w φ(m)]` (`aa_divR`) and the recursive divergence utility
  `U_t = u(c_t) + βR_t(U_{t+1})` (`aa_rdU`); with a fixed distortion, `aa_rdUm`.
* The time-zero formula: for fixed distortions,
  `U₀ = E ∑_t βᵗ M_t {u(c_t) + βθE_t[w_{t+1}φ(m_{t+1})]}` (with no penalty in the last period)
  (`aa_rdUm_eq_sum`), by unrolling under the distorted measure (`aa_rdUm_unroll`) and changing
  measure with the martingale `M` (`aa_Ex_change`).
* Dynamic consistency: the recursive utility is the infimum over all adapted distortion processes of
  the time-zero formula (`aa_rdU_isGLB`), so the recursion and the time-zero minimisation agree.
* With relative entropy and `w = 1`, `R_t` is the risk-sensitive operator
  `−θ ln E_t exp(−x/θ)` (`aa_divR_kl`): the recursive multiplier utility.

Departure: the book's horizon is infinite; here it is finite, and the infimum over distortions is an
infimum (it is attained, e.g., for relative entropy, `aa_divR_kl`).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- An admissible one-step-ahead density at a node with reference distribution `p`:
`m ≥ 0`, `E[m] = 1`. -/
def aa_Admissible (p m : S → ℝ) : Prop := (∀ s, 0 ≤ m s) ∧ ∑ s, p s * m s = 1

/-- The constant density `m = 1` (no distortion) is admissible. -/
theorem aa_admissible_one {p : S → ℝ} (hp : SS.IsDistribution p) : aa_Admissible p fun _ => 1 :=
  ⟨fun _ => zero_le_one, by simp [hp.sum_eq_one]⟩

/-- The distorted one-step distribution `π̂ = m π` is a distribution. -/
theorem aa_admissible_isDistribution {p m : S → ℝ} (hp : SS.IsDistribution p)
    (hm : aa_Admissible p m) : SS.IsDistribution fun s => p s * m s :=
  ⟨fun s => mul_nonneg (hp.nonneg s) (hm.1 s), hm.2⟩

/-- The martingale `M_{t+1} = m_{t+1}M_t`, `M₀ = 1`, of (20.8). -/
def aa_M (m : List S → S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => m h s * aa_M m h

/-- Miao, (20.8), p. 696: `M` is a martingale under the reference measure, `E_t M_{t+1} = M_t`. -/
theorem aa_M_martingale {p : List S → S → ℝ} {m : List S → S → ℝ}
    (hm : ∀ h, aa_Admissible (p h) (m h)) (h : List S) :
    ∑ s, p h s * aa_M m (s :: h) = aa_M m h := by
  simp only [aa_M, ← mul_assoc, ← Finset.sum_mul, (hm h).2, one_mul]

/-- The objective `E_t[m x + θ w φ(m)]` at a node. -/
def aa_divObj (p w : S → ℝ) (θ : ℝ) (φ : ℝ → ℝ) (x m : S → ℝ) : ℝ :=
  ∑ s, p s * (m s * x s + θ * w s * φ (m s))

/-- The divergence uncertainty aggregator `R_t(x) = inf_m E_t[m x + θwφ(m)]`, `E_t m = 1`. -/
noncomputable def aa_divR (p w : S → ℝ) (θ : ℝ) (φ : ℝ → ℝ) (x : S → ℝ) : ℝ :=
  sInf ((aa_divObj p w θ φ x) '' {m | aa_Admissible p m})

/-- The recursive divergence utility `U_t = u(c_t) + βR_t(U_{t+1})`, `U_T = u(c_T)`
(Miao, p. 696). -/
noncomputable def aa_rdU (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w : List S → S → ℝ)
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h => u (c h) + β * aa_divR (p h) (w h) θ φ fun s => aa_rdU u β θ φ p w c n (s :: h)

/-- The same recursion for a fixed adapted distortion process `m`. -/
def aa_rdUm (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w m : List S → S → ℝ)
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h =>
    u (c h) + β * aa_divObj (p h) (w h) θ φ (fun s => aa_rdUm u β θ φ p w m c n (s :: h)) (m h)

/-- The objective is bounded below on admissible densities (`θ, w, φ ≥ 0`). -/
theorem aa_divObj_ge {p w : S → ℝ} (hp : SS.IsDistribution p) (hw : ∀ s, 0 ≤ w s) {θ : ℝ}
    (hθ : 0 ≤ θ) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (x : S → ℝ) {m : S → ℝ}
    (hm : aa_Admissible p m) : -∑ s, |x s| ≤ aa_divObj p w θ φ x m := by
  have h1 := aa_E_ge_neg (aa_admissible_isDistribution hp hm) x
  have h2 : aa_E (fun s => p s * m s) x ≤ aa_divObj p w θ φ x m := by
    unfold aa_E aa_divObj
    refine Finset.sum_le_sum fun s _ => ?_
    have := mul_nonneg (mul_nonneg (mul_nonneg hθ (hw s)) (hφ (m s))) (hp.nonneg s)
    nlinarith
  linarith

theorem aa_divR_le {p w : S → ℝ} (hp : SS.IsDistribution p) (hw : ∀ s, 0 ≤ w s) {θ : ℝ}
    (hθ : 0 ≤ θ) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (x : S → ℝ) {m : S → ℝ}
    (hm : aa_Admissible p m) : aa_divR p w θ φ x ≤ aa_divObj p w θ φ x m :=
  csInf_le ⟨-∑ s, |x s|, by rintro _ ⟨m', hm', rfl⟩; exact aa_divObj_ge hp hw hθ hφ x hm'⟩
    ⟨m, hm, rfl⟩

/-- The objective changes by `E_t[m(x − y)]` when the continuation changes from `y` to `x`. -/
theorem aa_divObj_sub (p w : S → ℝ) (θ : ℝ) (φ : ℝ → ℝ) (x y m : S → ℝ) :
    aa_divObj p w θ φ x m - aa_divObj p w θ φ y m = ∑ s, p s * m s * (x s - y s) := by
  unfold aa_divObj
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `t`-step expectations under the distorted measure `π̂ = mπ`. -/
def aa_distort (p m : List S → S → ℝ) : List S → S → ℝ := fun h s => p h s * m h s

/-- Unrolling the recursion for a fixed distortion: under the distorted measure,
`U_n(h) = ∑_{t<n} βᵗ Ê_h[g(h_t)] + βⁿ Ê_h[u(c_{h_n})]` with the flow
`g = u(c_t) + βθE_t[wφ(m)]`. -/
theorem aa_rdUm_unroll (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w m : List S → S → ℝ)
    (c : List S → ℝ) (n : ℕ) (h : List S) :
    aa_rdUm u β θ φ p w m c n h =
      ∑ t ∈ Finset.range n, β ^ t * aa_Ex (aa_distort p m) t
          (fun h' => u (c h') + β * θ * ∑ s, p h' s * w h' s * φ (m h' s)) h +
        β ^ n * aa_Ex (aa_distort p m) n (fun h' => u (c h')) h := by
  refine aa_linear_unroll _ β _ _ (aa_rdUm u β θ φ p w m c) (fun _ => rfl) (fun n h => ?_) n h
  simp only [aa_rdUm, aa_divObj, aa_distort]
  rw [add_assoc]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Change of measure with the martingale `M`: `M(h) Ê_h[f(h_t)] = E_h[M(h_t) f(h_t)]`. -/
theorem aa_Ex_change (p m : List S → S → ℝ) (f : List S → ℝ) :
    ∀ t h, aa_M m h * aa_Ex (aa_distort p m) t f h =
      aa_Ex p t (fun h' => aa_M m h' * f h') h
  | 0, h => rfl
  | t + 1, h => by
    simp only [aa_Ex, aa_distort, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← aa_Ex_change p m f t (s :: h), aa_M]
    ring

/-- **The time-zero divergence utility** (Miao, p. 696): for a fixed adapted distortion process,
`U₀(c) = E ∑_{t<T} βᵗ M_t{u(c_t) + βθE_t[w_{t+1}φ(m_{t+1})]} + βᵀE[M_T u(c_T)]`; the penalty
terms form the discounted divergence `β ∑_t βᵗ E[M_t w_{t+1}φ(m_{t+1})]`. -/
theorem aa_rdUm_eq_sum (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w m : List S → S → ℝ)
    (c : List S → ℝ) (n : ℕ) :
    aa_rdUm u β θ φ p w m c n [] =
      ∑ t ∈ Finset.range n, β ^ t * aa_Ex p t
          (fun h' => aa_M m h' * (u (c h') + β * θ * ∑ s, p h' s * w h' s * φ (m h' s))) [] +
        β ^ n * aa_Ex p n (fun h' => aa_M m h' * u (c h')) [] := by
  rw [aa_rdUm_unroll]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [← aa_Ex_change, aa_M, one_mul]
  · rw [← aa_Ex_change, aa_M, one_mul]

/-- The recursive utility is a lower bound for every distortion process (`θ, w, φ ≥ 0`, `β ≥ 0`). -/
theorem aa_rdU_le_rdUm (u : ℝ → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hθ : 0 ≤ θ) {φ : ℝ → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) {p w m : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h))
    (hw : ∀ h s, 0 ≤ w h s) (hm : ∀ h, aa_Admissible (p h) (m h)) (c : List S → ℝ) :
    ∀ n h, aa_rdU u β θ φ p w c n h ≤ aa_rdUm u β θ φ p w m c n h
  | 0, h => le_rfl
  | n + 1, h => by
    simp only [aa_rdU, aa_rdUm]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hβ)
    refine (aa_divR_le (hp h) (hw h) hθ hφ _ (hm h)).trans ?_
    have := aa_divObj_sub (p h) (w h) θ φ (fun s => aa_rdUm u β θ φ p w m c n (s :: h))
      (fun s => aa_rdU u β θ φ p w c n (s :: h)) (m h)
    have h2 : 0 ≤ ∑ s, p h s * m h s *
        (aa_rdUm u β θ φ p w m c n (s :: h) - aa_rdU u β θ φ p w c n (s :: h)) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg ((hp h).nonneg s) ((hm h).1 s))
        (sub_nonneg.2 (aa_rdU_le_rdUm u hβ hθ hφ hp hw hm c n (s :: h)))
    linarith

/-- **Dynamic consistency of recursive divergence utility** (Miao, p. 696). For `0 ≤ β ≤ 1`,
`θ ≥ 0`, `w ≥ 0`, `φ ≥ 0`, the recursive utility at every node is the infimum, over all adapted
distortion processes, of the utility under a fixed distortion, which is the time-zero formula
`aa_rdUm_eq_sum`. -/
theorem aa_rdU_isGLB (u : ℝ → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 ≤ θ)
    {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {p w : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h))
    (hw : ∀ h s, 0 ≤ w h s) (c : List S → ℝ) (n : ℕ) (h : List S) :
    IsGLB {y | ∃ m : List S → S → ℝ, (∀ h', aa_Admissible (p h') (m h')) ∧
        y = aa_rdUm u β θ φ p w m c n h} (aa_rdU u β θ φ p w c n h) := by
  classical
  refine ⟨by rintro y ⟨m, hm, rfl⟩; exact aa_rdU_le_rdUm u hβ hθ hφ hp hw hm c n h, ?_⟩
  intro b hb
  by_contra hlt
  push Not at hlt
  set ε := b - aa_rdU u β θ φ p w c n h with hε
  have hε0 : 0 < ε := by linarith
  set δ := ε / (n + 1 : ℝ) with hδ
  have hδ0 : 0 < δ := by positivity
  set N := n + h.length with hN
  -- near-minimising densities at every node
  have hnear : ∀ h' : List S, ∃ m' : S → ℝ, aa_Admissible (p h') m' ∧
      aa_divObj (p h') (w h') θ φ
          (fun s => aa_rdU u β θ φ p w c (N - h'.length - 1) (s :: h')) m' <
        aa_divR (p h') (w h') θ φ
          (fun s => aa_rdU u β θ φ p w c (N - h'.length - 1) (s :: h')) + δ := by
    intro h'
    have hne : ((aa_divObj (p h') (w h') θ φ
        (fun s => aa_rdU u β θ φ p w c (N - h'.length - 1) (s :: h'))) ''
          {m | aa_Admissible (p h') m}).Nonempty :=
      ⟨_, _, aa_admissible_one (hp h'), rfl⟩
    obtain ⟨_, ⟨m', hm', rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hδ0)
    exact ⟨m', hm', hlt'⟩
  choose m hm hmlt using hnear
  have key : ∀ k h', h'.length + k = N →
      aa_rdUm u β θ φ p w m c k h' ≤ aa_rdU u β θ φ p w c k h' + k * δ := by
    intro k
    induction k with
    | zero => intro h' _; simp [aa_rdUm, aa_rdU]
    | succ k ih =>
      intro h' hlen
      have hidx : N - h'.length - 1 = k := by omega
      have hm' := hmlt h'
      rw [hidx] at hm'
      simp only [aa_rdU, aa_rdUm]
      have hsub := aa_divObj_sub (p h') (w h') θ φ
        (fun s => aa_rdUm u β θ φ p w m c k (s :: h'))
        (fun s => aa_rdU u β θ φ p w c k (s :: h')) (m h')
      have hbound : ∑ s, p h' s * m h' s *
          (aa_rdUm u β θ φ p w m c k (s :: h') - aa_rdU u β θ φ p w c k (s :: h')) ≤ k * δ := by
        calc ∑ s, p h' s * m h' s *
              (aa_rdUm u β θ φ p w m c k (s :: h') - aa_rdU u β θ φ p w c k (s :: h'))
            ≤ ∑ s, p h' s * m h' s * (k * δ) :=
              Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
                (by linarith [ih (s :: h') (by simp only [List.length_cons]; omega)])
                (mul_nonneg ((hp h').nonneg s) ((hm h').1 s))
          _ = k * δ := by rw [← Finset.sum_mul, (hm h').2, one_mul]
      have h3 : aa_divObj (p h') (w h') θ φ (fun s => aa_rdUm u β θ φ p w m c k (s :: h')) (m h')
          ≤ aa_divR (p h') (w h') θ φ (fun s => aa_rdU u β θ φ p w c k (s :: h')) +
            (k * δ + δ) := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hβ
      have h5 : β * (k * δ + δ) ≤ (k + 1 : ℕ) * δ := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hδ0.le]
      nlinarith
  have := key n h (by omega)
  have hnδ : (n : ℝ) * δ < ε := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hb' := hb ⟨m, hm, rfl⟩
  linarith

/-- Miao, pp. 695–696: with relative entropy, `w = 1` and a full-support reference distribution,
`R_t(x) = min_m E_t[m x + θ m ln m − θ m + θ] = −θ ln E_t exp(−x/θ)`: recursive divergence utility
is the recursive multiplier (risk-sensitive) utility. -/
theorem aa_divR_kl {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (x : S → ℝ) :
    aa_divR p (fun _ => 1) θ aa_klPhi x = -θ * Real.log (∑ s, p s * Real.exp (-x s / θ)) := by
  rw [← aa_divU_kl hθ hp hpos x]
  unfold aa_divR aa_divU aa_variational
  congr 1
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨fun s => p s * m s, aa_admissible_isDistribution hp hm, ?_⟩
    simp only [aa_E, aa_phiDiv, aa_divObj, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [mul_div_cancel_left₀ _ (hpos s).ne']
      ring
  · rintro ⟨q, hq, rfl⟩
    refine ⟨fun s => q s / p s, ⟨fun s => div_nonneg (hq.nonneg s) (hpos s).le, ?_⟩, ?_⟩
    · rw [← hq.sum_eq_one]
      exact Finset.sum_congr rfl fun s _ => by field_simp [(hpos s).ne']
    · simp only [aa_E, aa_phiDiv, aa_divObj, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by
        field_simp [(hpos s).ne']

end Miao.RecursiveUtility

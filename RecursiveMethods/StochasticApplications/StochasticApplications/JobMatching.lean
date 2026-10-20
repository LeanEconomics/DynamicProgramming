/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.SearchDynamics

/-!
# A model of job matching

SLP §10.10, pp. 311–314, Exercise 10.10d–h. A worker who has had `k` successes in `n` periods
on a task expects to succeed with probability `π(n, k)`. Staying earns `π(n, k)` and moves the
state to `(n + 1, k + 1)` or `(n + 1, k)`; a new task does the same from `(0, 0)`:
`v(n, k) = max {π(n, k) + β[π(n, k)v(n + 1, k + 1) + (1 − π(n, k))v(n + 1, k)], v-stay(0, 0)}` (1),
on the triangular array `D = {(n, k) : k ≤ n}` (`triD`).

* **Exercise 10.10f** (`ex_10_10f`): for any `π` with values in `[0, 1]`, (1) has a unique bounded
  solution, and it lies in `S = {f : D → [0, 1/(1 − β)]}` (Blackwell's conditions).
* **Exercise 10.10g** (`ex_10_10g`): if `π` has the properties of part (d) (`PiProps`),
  `v(n, k)` is nonincreasing in `n`, nondecreasing in `k`, and nondecreasing along
  `(n, k) ↦ (n + 1, k + 1)`. If `π` is uniformly near `p` on the windows
  `{(n + j, kₙ + i) : i ≤ j ≤ J}` for large `n`, then `v(n, kₙ) → max{p/(1 − β), v(0, 0)}`
  (`ex_10_10g_limit`); the beta-prior `π` satisfies this when `kₙ/n → p`
  (`betaπ_window`, `ex_10_10g_beta` in `BetaPosterior`).
* **Exercise 10.10h** (`ex_10_10h`): staying when indifferent, the optimal policy is
  `g(n, k) = 1` iff `k ≥ jₙ`, with `j₁ = 1` and `jₙ₊₁ ≥ jₙ`.
* Exercise 10.10a–e, for the beta prior, are in `BetaPosterior`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open Set Filter Topology BoundedContinuousFunction

/-- The triangular array `D = {(n, k) : k ≤ n}`. -/
def triD : Set (ℕ × ℕ) := {p | p.2 ≤ p.1}

/-- A success: `(n, k) ↦ (n + 1, k + 1)`. -/
def triS (p : triD) : triD := ⟨(p.1.1 + 1, p.1.2 + 1), Nat.succ_le_succ p.2⟩

/-- A failure: `(n, k) ↦ (n + 1, k)`. -/
def triF (p : triD) : triD := ⟨(p.1.1 + 1, p.1.2), Nat.le_succ_of_le p.2⟩

/-- One more success at the same date: `(n, k) ↦ (n, k + 1)`, for `k < n`. -/
def triK (p : triD) (h : p.1.2 + 1 ≤ p.1.1) : triD := ⟨(p.1.1, p.1.2 + 1), h⟩

/-- The state of a new task. -/
def tri00 : triD := ⟨(0, 0), show (0 : ℕ) ≤ 0 from le_rfl⟩

/-- The point `(n, k)` of `D`. -/
def triMk (n k : ℕ) (h : k ≤ n) : triD := ⟨(n, k), h⟩

variable (π : ℕ → ℕ → ℝ) (β : ℝ)

/-- The value of staying on the task: `π + β[π f(n + 1, k + 1) + (1 − π) f(n + 1, k)]`. -/
def stayV (f : triD → ℝ) (p : triD) : ℝ :=
  π p.1.1 p.1.2 + β * (π p.1.1 p.1.2 * f (triS p) + (1 - π p.1.1 p.1.2) * f (triF p))

/-- The return of staying, `q + β[q a + (1 − q) b]`, is nondecreasing in the continuation values,
and in the success probability `q` when `a ≥ b`; strictly so in `q`. -/
theorem stay_le {β : ℝ} (hβ : 0 ≤ β) {q q' a b a' b' : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqq' : q ≤ q') (hba : b' ≤ a') (ha : a ≤ a') (hb : b ≤ b') :
    q + β * (q * a + (1 - q) * b) ≤ q' + β * (q' * a' + (1 - q') * b') := by
  have h1 : q * a + (1 - q) * b ≤ q * a' + (1 - q) * b' := by
    nlinarith [mul_le_mul_of_nonneg_left ha hq, mul_le_mul_of_nonneg_left hb (sub_nonneg.2 hq1)]
  have h2 : 0 ≤ (q' - q) * (1 + β * (a' - b')) :=
    mul_nonneg (by linarith) (by nlinarith [mul_nonneg hβ (sub_nonneg.2 hba)])
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ]

theorem stay_lt {β : ℝ} (hβ : 0 ≤ β) {q q' a b a' b' : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqq' : q < q') (hba : b' ≤ a') (ha : a ≤ a') (hb : b ≤ b') :
    q + β * (q * a + (1 - q) * b) < q' + β * (q' * a' + (1 - q') * b') := by
  have h1 : q * a + (1 - q) * b ≤ q * a' + (1 - q) * b' := by
    nlinarith [mul_le_mul_of_nonneg_left ha hq, mul_le_mul_of_nonneg_left hb (sub_nonneg.2 hq1)]
  have h2 : 0 < (q' - q) * (1 + β * (a' - b')) :=
    mul_pos (by linarith) (by nlinarith [mul_nonneg hβ (sub_nonneg.2 hba)])
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ]

variable {π β}

theorem abs_stayV_le (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ : 0 ≤ β) (f : triD →ᵇ ℝ)
    (p : triD) : |stayV π β f p| ≤ 1 + β * ‖f‖ := by
  obtain ⟨h0, h1⟩ := hπ p.1.1 p.1.2 p.2
  have hS := (abs_le.1 ((Real.norm_eq_abs _).symm.le.trans (f.norm_coe_le_norm (triS p))))
  have hF := (abs_le.1 ((Real.norm_eq_abs _).symm.le.trans (f.norm_coe_le_norm (triF p))))
  rw [abs_le]
  unfold stayV
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hS.1 h0, mul_le_mul_of_nonneg_left hS.2 h0,
    mul_le_mul_of_nonneg_left hF.1 (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hF.2
      (sub_nonneg.2 h1), norm_nonneg f]

/-- The operator `T` of the functional equation (1). -/
noncomputable def jobT (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ : 0 ≤ β) (f : triD →ᵇ ℝ) :
    triD →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun p => max (stayV π β f p) (stayV π β f tri00)) (1 + β * ‖f‖)
    fun p => by
      rw [Real.norm_eq_abs]
      exact abs_max_le_max_abs_abs.trans (max_le (abs_stayV_le hπ hβ f p)
        (abs_stayV_le hπ hβ f tri00))

theorem jobT_apply (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ : 0 ≤ β) (f : triD →ᵇ ℝ)
    (p : triD) :
    jobT hπ hβ f p = max (stayV π β f p) (stayV π β f tri00) := rfl

theorem jobT_contraction (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsContraction (jobT hπ hβ0.le) β := by
  have hmono : ∀ (f g : triD →ᵇ ℝ) (p : triD), f ≤ g → stayV π β f p ≤ stayV π β g p :=
    fun f g p hfg => by
      obtain ⟨h0, h1⟩ := hπ p.1.1 p.1.2 p.2
      have hS : f (triS p) ≤ g (triS p) := hfg (triS p)
      have hF : f (triF p) ≤ g (triF p) := hfg (triF p)
      have hmix : π p.1.1 p.1.2 * f (triS p) + (1 - π p.1.1 p.1.2) * f (triF p) ≤
          π p.1.1 p.1.2 * g (triS p) + (1 - π p.1.1 p.1.2) * g (triF p) := by
        nlinarith [mul_le_mul_of_nonneg_left hS h0, mul_le_mul_of_nonneg_left hF
          (sub_nonneg.2 h1)]
      unfold stayV
      nlinarith [mul_le_mul_of_nonneg_left hmix hβ0.le]
  refine ⟨hβ0, hβ1, blackwell hβ0.le (fun f g hfg p => ?_) (fun f a _ p => ?_)⟩
  · change jobT hπ hβ0.le f p ≤ jobT hπ hβ0.le g p
    rw [jobT_apply, jobT_apply]
    exact max_le_max (hmono f g p hfg) (hmono f g tri00 hfg)
  · have hs : ∀ q, stayV π β ((f + const triD a : triD →ᵇ ℝ) : triD → ℝ) q =
        stayV π β f q + β * a := fun q => by
      simp only [stayV, coe_add, Pi.add_apply, const_apply]; ring
    change jobT hπ hβ0.le (f + const triD a) p ≤ jobT hπ hβ0.le f p + β * a
    rw [jobT_apply, jobT_apply, hs, hs, max_add_add_right]

/-- **Exercise 10.10f.** For any `π` with values in `[0, 1]` and `0 < β < 1`, (1) has a unique
bounded solution `v`, and `0 ≤ v ≤ 1/(1 − β)`: `v` is the unique solution in `S`. -/
theorem ex_10_10f (hπ : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v : triD →ᵇ ℝ, jobT hπ hβ0.le v = v ∧ (∀ w, jobT hπ hβ0.le w = w → w = v) ∧
      ∀ p, 0 ≤ v p ∧ v p ≤ 1 / (1 - β) := by
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (jobT_contraction hπ hβ0 hβ1)
  refine ⟨v, hv, huniq, ?_⟩
  set S' : Set (triD →ᵇ ℝ) := {f | ∀ p, 0 ≤ f p ∧ f p ≤ 1 / (1 - β)}
  have hclosed : IsClosed S' := by
    have : S' = ⋂ p, ({f : triD →ᵇ ℝ | 0 ≤ f p} ∩ {f | f p ≤ 1 / (1 - β)}) := by
      ext f; simp [S']
    rw [this]
    exact isClosed_iInter fun p => (isClosed_le continuous_const (continuous_eval_const p)).inter
      (isClosed_le (continuous_eval_const p) continuous_const)
  have hb1 : 0 < 1 - β := by linarith
  have hmaps : MapsTo (jobT hπ hβ0.le) S' S' := by
    intro f hf p
    have hs : ∀ q, 0 ≤ stayV π β f q ∧ stayV π β f q ≤ 1 / (1 - β) := fun q => by
      obtain ⟨h0, h1⟩ := hπ q.1.1 q.1.2 q.2
      obtain ⟨hS0, hS1⟩ := hf (triS q)
      obtain ⟨hF0, hF1⟩ := hf (triF q)
      unfold stayV
      constructor
      · have : 0 ≤ 1 - π q.1.1 q.1.2 := by linarith
        positivity
      · have e : 1 / (1 - β) = 1 + β * (1 / (1 - β)) := by field_simp; ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hS1 h0, mul_le_mul_of_nonneg_left hF1
          (sub_nonneg.2 h1)]
    rw [jobT_apply]
    exact ⟨(hs p).1.trans (le_max_left _ _), max_le (hs p).2 (hs tri00).2⟩
  exact (corollary_1 (jobT_contraction hπ hβ0 hβ1) hv
    ⟨0, fun _ => ⟨le_rfl, show (0 : ℝ) ≤ 1 / (1 - β) from div_nonneg zero_le_one hb1.le⟩⟩
    hclosed hmaps hmaps).1

/-! ### Exercise 10.10g: monotonicity -/

/-- The properties of `π(n, k)` in Exercise 10.10d. -/
structure PiProps (π : ℕ → ℕ → ℝ) : Prop where
  bounds : ∀ n k, k ≤ n → 0 < π n k ∧ π n k < 1
  succ_k : ∀ n k, k + 1 ≤ n → π n k < π n (k + 1)
  succ_n : ∀ n k, k ≤ n → π (n + 1) k < π n k
  succ_nk : ∀ n k, k ≤ n → π n k < π (n + 1) (k + 1)

/-- The closed set of functions nonincreasing in `n`, nondecreasing in `k`, and nondecreasing
along successes. -/
def jobMono : Set (triD →ᵇ ℝ) :=
  {f | (∀ p, f (triF p) ≤ f p) ∧ (∀ p h, f p ≤ f (triK p h)) ∧ ∀ p, f p ≤ f (triS p)}

theorem isClosed_jobMono : IsClosed jobMono := by
  have h1 : IsClosed {f : triD →ᵇ ℝ | ∀ p, f (triF p) ≤ f p} := by
    have : {f : triD →ᵇ ℝ | ∀ p, f (triF p) ≤ f p} = ⋂ p, {f | f (triF p) ≤ f p} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun p => isClosed_le (continuous_eval_const _) (continuous_eval_const _)
  have h2 : IsClosed {f : triD →ᵇ ℝ | ∀ p h, f p ≤ f (triK p h)} := by
    have : {f : triD →ᵇ ℝ | ∀ p h, f p ≤ f (triK p h)} =
        ⋂ p, ⋂ h, {f | f p ≤ f (triK p h)} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun p => isClosed_iInter fun h =>
      isClosed_le (continuous_eval_const _) (continuous_eval_const _)
  have h3 : IsClosed {f : triD →ᵇ ℝ | ∀ p, f p ≤ f (triS p)} := by
    have : {f : triD →ᵇ ℝ | ∀ p, f p ≤ f (triS p)} = ⋂ p, {f | f p ≤ f (triS p)} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun p => isClosed_le (continuous_eval_const _) (continuous_eval_const _)
  exact h1.inter (h2.inter h3)

/-- The stay value inherits the three monotonicity properties. -/
theorem stayV_mono (hπ : PiProps π) (hβ : 0 ≤ β) {f : triD →ᵇ ℝ} (hf : f ∈ jobMono) :
    (∀ p, stayV π β f (triF p) ≤ stayV π β f p) ∧
      (∀ p h, stayV π β f p ≤ stayV π β f (triK p h)) ∧
      (∀ p, stayV π β f p ≤ stayV π β f (triS p)) := by
  obtain ⟨hn, hk, hd⟩ := hf
  refine ⟨fun p => ?_, fun p h => ?_, fun p => ?_⟩
  · -- `(n + 1, k)` against `(n, k)`
    obtain ⟨h0, h1⟩ := hπ.bounds _ _ (triF p).2
    exact stay_le hβ h0.le h1.le (hπ.succ_n _ _ p.2).le (hk (triF p) (Nat.succ_le_succ p.2))
      (hn (triS p)) (hn (triF p))
  · -- `(n, k)` against `(n, k + 1)`
    obtain ⟨h0, h1⟩ := hπ.bounds _ _ p.2
    exact stay_le hβ h0.le h1.le (hπ.succ_k _ _ h).le (hk (triS p) (Nat.succ_le_succ h))
      (hk (triS p) (Nat.succ_le_succ h)) (hk (triF p) (Nat.succ_le_succ p.2))
  · -- `(n, k)` against `(n + 1, k + 1)`
    obtain ⟨h0, h1⟩ := hπ.bounds _ _ p.2
    exact stay_le hβ h0.le h1.le (hπ.succ_nk _ _ p.2).le
      (hk (triF (triS p)) (Nat.succ_le_succ (Nat.succ_le_succ p.2))) (hd (triS p)) (hd (triF p))

/-- **Exercise 10.10g** (monotonicity). With `π` as in part (d), `v(n, k)` is nonincreasing in
`n`, nondecreasing in `k`, and nondecreasing along `(n, k) ↦ (n + 1, k + 1)`. -/
theorem ex_10_10g (hπ : PiProps π) (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {v : triD →ᵇ ℝ} (hv : jobT hπ01 hβ0.le v = v) : v ∈ jobMono := by
  have hmaps : MapsTo (jobT hπ01 hβ0.le) jobMono jobMono := by
    intro f hf
    obtain ⟨hn, hk, hd⟩ := stayV_mono hπ hβ0.le hf
    refine ⟨fun p => ?_, fun p h => ?_, fun p => ?_⟩ <;> simp only [jobT_apply]
    · exact max_le_max (hn p) le_rfl
    · exact max_le_max (hk p h) le_rfl
    · exact max_le_max (hd p) le_rfl
  exact (corollary_1 (S' := jobMono) (S'' := jobMono) (jobT_contraction hπ01 hβ0 hβ1) hv
    ⟨0, fun _ => le_rfl, fun _ _ => le_rfl, fun _ => le_rfl⟩ isClosed_jobMono hmaps hmaps).1

/-! ### Exercise 10.10h: the threshold policy -/

/-- **Exercise 10.10h.** Staying when indifferent, the worker stays on a task at `(n, k)` iff
`k ≥ jₙ`, where `j₁ = 1` and `jₙ` is nondecreasing. -/
theorem ex_10_10h (hπ : PiProps π) (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {v : triD →ᵇ ℝ} (hv : jobT hπ01 hβ0.le v = v) :
    ∃ j : ℕ → ℕ, (∀ p : triD, v tri00 ≤ stayV π β v p ↔ j p.1.1 ≤ p.1.2) ∧ j 1 = 1 ∧
      Monotone j := by
  obtain ⟨hn, hk, hd⟩ := ex_10_10g hπ hπ01 hβ0 hβ1 hv
  obtain ⟨sn, sk, -⟩ := stayV_mono hπ hβ0.le (ex_10_10g hπ hπ01 hβ0 hβ1 hv)
  have hv00 : v tri00 = stayV π β v tri00 := by
    conv_lhs => rw [← hv, jobT_apply, max_self]
  -- stay at `(n, k)` iff `stay(n, k) ≥ v(0, 0)`; the set of such `k` is an up-set
  set P : ℕ → ℕ → Prop := fun n k => k = n + 1 ∨ ∃ h : k ≤ n, v tri00 ≤ stayV π β v (triMk n k h)
  have hex : ∀ n, ∃ k, P n k := fun n => ⟨n + 1, Or.inl rfl⟩
  classical
  set j : ℕ → ℕ := fun n => Nat.find (hex n)
  have hj_le : ∀ n, j n ≤ n + 1 := fun n => Nat.find_min' (hex n) (Or.inl rfl)
  -- `stay(n, ·)` is monotone in `k`
  have hsk : ∀ n k d (h : k + d ≤ n),
      stayV π β v (triMk n k (by omega)) ≤ stayV π β v (triMk n (k + d) h) := by
    intro n k d
    induction d with
    | zero => intro h; exact le_rfl
    | succ d ih =>
      intro h
      exact (ih (by omega)).trans (sk (triMk n (k + d) (by omega)) h)
  have hchar : ∀ p : triD, v tri00 ≤ stayV π β v p ↔ j p.1.1 ≤ p.1.2 := by
    rintro ⟨⟨n, k⟩, hkn⟩
    change v tri00 ≤ stayV π β v (triMk n k hkn) ↔ j n ≤ k
    constructor
    · intro h
      exact Nat.find_min' (hex n) (Or.inr ⟨hkn, h⟩)
    · intro h
      rcases Nat.find_spec (hex n) with h' | ⟨hjn, h'⟩
      · exfalso
        change j n = n + 1 at h'
        change j n ≤ k at h
        have : k ≤ n := hkn
        omega
      · obtain ⟨d, hd⟩ : ∃ d, k = j n + d := ⟨k - j n, by omega⟩
        subst hd
        exact h'.trans (hsk n (j n) d hkn)
  refine ⟨j, hchar, ?_, monotone_nat_of_le_succ fun n => ?_⟩
  · -- `j₁ = 1`: leave after one failure, stay after one success
    have hπ00 := hπ.bounds 0 0 le_rfl
    have hπ10 := hπ.bounds 1 0 (by norm_num)
    have hπ11 := hπ.bounds 1 1 le_rfl
    have h10 : stayV π β v (triMk 1 0 (by norm_num)) < v tri00 := by
      rw [hv00]
      exact stay_lt hβ0.le hπ10.1.le hπ10.2.le (hπ.succ_n 0 0 le_rfl) (hk (triF tri00) le_rfl)
        (hn (triS tri00)) (hn (triF tri00))
    have h11 : v tri00 ≤ stayV π β v (triMk 1 1 le_rfl) := by
      rw [hv00]
      exact (stay_lt hβ0.le hπ00.1.le hπ00.2.le (hπ.succ_nk 0 0 le_rfl)
        (hk (triF (triS tri00)) (show 1 + 1 ≤ 2 from le_rfl)) (hd (triS tri00))
        (hd (triF tri00))).le
    have hj1 : j 1 ≤ 1 := (hchar (triMk 1 1 le_rfl)).1 h11
    have hj0 : ¬ j 1 ≤ 0 := fun h => not_le.2 h10 ((hchar (triMk 1 0 (by norm_num))).2 h)
    omega
  · -- `jₙ ≤ jₙ₊₁`: staying at `(n + 1, k)` implies staying at `(n, k)`
    by_cases hk' : j (n + 1) ≤ n
    · have hstay := (hchar (triMk (n + 1) (j (n + 1)) (by omega))).2 le_rfl
      have := sn (triMk n (j (n + 1)) hk')
      exact (hchar (triMk n (j (n + 1)) hk')).1 (hstay.trans this)
    · exact (hj_le n).trans (by omega)

/-! ### Exercise 10.10g: the limit -/

/-- The bound sequence `G₀ = 1/(1 − β)`, `Gₘ₊₁ = max{v(0, 0), q + βGₘ}`. -/
noncomputable def jobG (β c q : ℝ) : ℕ → ℝ
  | 0 => 1 / (1 - β)
  | m + 1 => max c (q + β * jobG β c q m)

/-- If `π ≤ q` at all states within `m` steps of `b`, then `v(b) ≤ Gₘ`. -/
theorem job_v_le (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) {v : triD →ᵇ ℝ}
    (hv : jobT hπ01 hβ0.le v = v) (hvb : ∀ p, v p ≤ 1 / (1 - β)) {q : ℝ} (m : ℕ) :
    ∀ b : triD, (∀ j i, i ≤ j → j < m → π (b.1.1 + j) (b.1.2 + i) ≤ q) →
      v b ≤ jobG β (v tri00) q m := by
  induction m with
  | zero => exact fun b _ => hvb b
  | succ m ih =>
    intro b hb
    have hS := ih (triS b) fun j i hij hjm => by
      have := hb (j + 1) (i + 1) (by omega) (by omega)
      simpa [triS, Nat.add_assoc, Nat.add_comm 1] using this
    have hF := ih (triF b) fun j i hij hjm => by
      have := hb (j + 1) i (by omega) (by omega)
      simpa [triF, Nat.add_assoc, Nat.add_comm 1] using this
    have hq := hb 0 0 le_rfl (Nat.succ_pos m)
    simp only [Nat.add_zero] at hq
    obtain ⟨h0, h1⟩ := hπ01 b.1.1 b.1.2 b.2
    conv_lhs => rw [← hv]
    rw [jobT_apply]
    refine max_le ?_ ?_
    · refine (le_max_right _ _).trans' ?_
      have hmix : π b.1.1 b.1.2 * v (triS b) + (1 - π b.1.1 b.1.2) * v (triF b) ≤
          jobG β (v tri00) q m := by
        nlinarith [mul_le_mul_of_nonneg_left hS h0, mul_le_mul_of_nonneg_left hF
          (sub_nonneg.2 h1)]
      have := mul_le_mul_of_nonneg_left hmix hβ0.le
      unfold stayV
      linarith
    · conv_lhs => rw [show stayV π β v tri00 = v tri00 by
        conv_rhs => rw [← hv, jobT_apply, max_self]]
      exact le_max_left _ _

/-- If `π ≥ q` at all states within `m` steps of `b`, then
`v(b) ≥ q + βq + ⋯ + βᵐ⁻¹q`. -/
theorem job_v_ge (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) {v : triD →ᵇ ℝ}
    (hv : jobT hπ01 hβ0.le v = v) (hv0 : ∀ p, 0 ≤ v p) {q : ℝ} (m : ℕ) :
    ∀ b : triD, (∀ j i, i ≤ j → j < m → q ≤ π (b.1.1 + j) (b.1.2 + i)) →
      ∑ t ∈ Finset.range m, β ^ t * q ≤ v b := by
  induction m with
  | zero => exact fun b _ => by simpa using hv0 b
  | succ m ih =>
    intro b hb
    have hS := ih (triS b) fun j i hij hjm => by
      have := hb (j + 1) (i + 1) (by omega) (by omega)
      simpa [triS, Nat.add_assoc, Nat.add_comm 1] using this
    have hF := ih (triF b) fun j i hij hjm => by
      have := hb (j + 1) i (by omega) (by omega)
      simpa [triF, Nat.add_assoc, Nat.add_comm 1] using this
    have hq := hb 0 0 le_rfl (Nat.succ_pos m)
    simp only [Nat.add_zero] at hq
    obtain ⟨h0, h1⟩ := hπ01 b.1.1 b.1.2 b.2
    conv_rhs => rw [← hv]
    rw [jobT_apply]
    refine le_trans ?_ (le_max_left _ _)
    rw [Finset.sum_range_succ', pow_zero, one_mul]
    have hsum : ∑ t ∈ Finset.range m, β ^ (t + 1) * q = β * ∑ t ∈ Finset.range m, β ^ t * q := by
      rw [Finset.mul_sum]; congr 1; ext t; ring
    rw [hsum]
    have hmix : ∑ t ∈ Finset.range m, β ^ t * q ≤
        π b.1.1 b.1.2 * v (triS b) + (1 - π b.1.1 b.1.2) * v (triF b) := by
      nlinarith [mul_le_mul_of_nonneg_left hS h0, mul_le_mul_of_nonneg_left hF (sub_nonneg.2 h1)]
    have := mul_le_mul_of_nonneg_left hmix hβ0.le
    unfold stayV
    linarith

/-- `Gₘ` converges geometrically to `max{c, q/(1 − β)}`. -/
theorem jobG_dist (hβ0 : 0 < β) (hβ1 : β < 1) (c q : ℝ) (m : ℕ) :
    |jobG β c q m - max c (q / (1 - β))| ≤ β ^ m * |1 / (1 - β) - max c (q / (1 - β))| := by
  have hb1 : 0 < 1 - β := by linarith
  have hfix : max c (q + β * max c (q / (1 - β))) = max c (q / (1 - β)) := by
    rcases le_total c (q / (1 - β)) with h | h
    · rw [max_eq_right h, show q + β * (q / (1 - β)) = q / (1 - β) by field_simp; ring,
        max_eq_right h]
    · rw [max_eq_left h]
      apply max_eq_left
      have : q ≤ c * (1 - β) := by rwa [div_le_iff₀ hb1] at h
      nlinarith
  induction m with
  | zero => rw [pow_zero, one_mul]; exact le_rfl
  | succ m ih =>
    have e : jobG β c q (m + 1) = max c (q + β * jobG β c q m) := rfl
    calc |jobG β c q (m + 1) - max c (q / (1 - β))|
        = |max c (q + β * jobG β c q m) - max c (q + β * max c (q / (1 - β)))| := by
          rw [e, hfix]
      _ ≤ |(q + β * jobG β c q m) - (q + β * max c (q / (1 - β)))| := by
          rw [max_comm c, max_comm c]; exact abs_max_sub_max_le_abs _ _ _
      _ = β * |jobG β c q m - max c (q / (1 - β))| := by
          rw [show q + β * jobG β c q m - (q + β * max c (q / (1 - β))) =
            β * (jobG β c q m - max c (q / (1 - β))) by ring, abs_mul, abs_of_pos hβ0]
      _ ≤ β * (β ^ m * |1 / (1 - β) - max c (q / (1 - β))|) :=
          mul_le_mul_of_nonneg_left ih hβ0.le
      _ = _ := by ring

/-- **Exercise 10.10g** (limit). If `π` is uniformly within any `ε` of `p` on the windows
`{(n + j, kₙ + i) : i ≤ j ≤ J}` for all large `n`, then `v(n, kₙ) → max{p/(1 − β), v(0, 0)}`. -/
theorem ex_10_10g_limit (hπ01 : ∀ n k, k ≤ n → 0 ≤ π n k ∧ π n k ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {v : triD →ᵇ ℝ} (hv : jobT hπ01 hβ0.le v = v) {k : ℕ → ℕ} (hk : ∀ n, k n ≤ n) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1)
    (hwin : ∀ (J : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∀ j i, i ≤ j → j ≤ J →
      |π (n + j) (k n + i) - p| ≤ ε) :
    Tendsto (fun n => v (triMk n (k n) (hk n))) atTop
      (𝓝 (max (p / (1 - β)) (v tri00))) := by
  obtain ⟨-, -, hvb⟩ := ex_10_10f hπ01 hβ0 hβ1
  obtain ⟨v', hv', huniq, hb⟩ := ex_10_10f hπ01 hβ0 hβ1
  have hvv' : v = v' := huniq v hv
  subst hvv'
  have hb1 : 0 < 1 - β := by linarith
  set c := v tri00
  have hc : 0 ≤ c ∧ c ≤ 1 / (1 - β) := hb tri00
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `m` with `βᵐ · 4/(1 − β) < ε/2`, then `δ ≤ 1` with `δ/(1 − β) ≤ ε/4`
  obtain ⟨m, hm⟩ := (tendsto_order.1 ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (4 / (1 - β)))).2 (ε / 2) (by rw [zero_mul]; linarith) |>.exists
  set δ := min (ε * (1 - β) / 4) 1
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ / (1 - β) ≤ ε / 4 := by
    rw [div_le_iff₀ hb1]; have := min_le_left (ε * (1 - β) / 4) 1; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hwin m δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  have hw := hN n hn
  set b := triMk n (k n) (hk n)
  have hup : v b ≤ jobG β c (p + δ) m := job_v_le hπ01 hβ0 hv (fun q => (hb q).2) m b
    fun j i hij hjm => by
      have := (abs_le.1 (hw j i hij hjm.le)).2
      change π (n + j) (k n + i) ≤ p + δ
      linarith
  have hlow : ∑ t ∈ Finset.range m, β ^ t * (p - δ) ≤ v b :=
    job_v_ge hπ01 hβ0 hv (fun q => (hb q).1) m b fun j i hij hjm => by
      have := (abs_le.1 (hw j i hij hjm.le)).1
      change p - δ ≤ π (n + j) (k n + i)
      linarith
  have hlow' : c ≤ v b := by
    rw [← hv, jobT_apply]
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    change v tri00 = stayV π β v tri00
    conv_lhs => rw [← hv, jobT_apply, max_self]
  have hgeo : ∑ t ∈ Finset.range m, β ^ t * (p - δ) = (p - δ) * (1 - β ^ m) / (1 - β) := by
    have hb' : β - 1 ≠ 0 := by linarith
    rw [← Finset.sum_mul, geom_sum_eq hβ1.ne, div_mul_eq_mul_div,
      div_eq_div_iff hb' hb1.ne']
    ring
  have hG := (abs_le.1 (jobG_dist hβ0 hβ1 c (p + δ) m)).2
  have hβm : 0 ≤ β ^ m := pow_nonneg hβ0.le m
  have hm' : β ^ m * (4 / (1 - β)) < ε / 2 := hm
  have hinv : 0 < 1 / (1 - β) := by positivity
  -- the limit of the bound sequence is within `ε/4` of `max{p/(1 − β), c}`
  have hstar : max c ((p + δ) / (1 - β)) ≤ max (p / (1 - β)) c + ε / 4 := by
    refine max_le (by linarith [le_max_right (p / (1 - β)) c]) ?_
    rw [add_div]
    linarith [le_max_left (p / (1 - β)) c]
  have hG0 : |1 / (1 - β) - max c ((p + δ) / (1 - β))| ≤ 4 / (1 - β) := by
    have h2 : (p + δ) / (1 - β) ≤ 2 / (1 - β) :=
      div_le_div_of_nonneg_right (by linarith) hb1.le
    have h3 : 1 / (1 - β) ≤ 2 / (1 - β) := div_le_div_of_nonneg_right (by norm_num) hb1.le
    have h4 : 2 / (1 - β) ≤ 4 / (1 - β) := div_le_div_of_nonneg_right (by norm_num) hb1.le
    rw [abs_le]
    constructor
    · linarith [max_le (hc.2.trans h3) h2]
    · linarith [le_max_left c ((p + δ) / (1 - β)), hc.1]
  have hupper : v b < max (p / (1 - β)) c + ε := by
    have := mul_le_mul_of_nonneg_left hG0 hβm
    linarith
  -- staying forever gives at least `(p − δ)(1 − βᵐ)/(1 − β)`
  have hL : p / (1 - β) - 3 * ε / 4 ≤ (p - δ) * (1 - β ^ m) / (1 - β) := by
    have e : (p - δ) * (1 - β ^ m) / (1 - β) =
        p / (1 - β) - δ / (1 - β) - β ^ m * (p / (1 - β)) + β ^ m * (δ / (1 - β)) := by
      field_simp
      ring
    have hp' : β ^ m * (p / (1 - β)) ≤ β ^ m * (4 / (1 - β)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hb1.le) hβm
    have : 0 ≤ β ^ m * (δ / (1 - β)) := mul_nonneg hβm (by positivity)
    linarith
  have hlower : max (p / (1 - β)) c - ε < v b := by
    rw [hgeo] at hlow
    rcases le_total (p / (1 - β)) c with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SequenceSupport

/-!
# A peculiar example (§16.6): the model and Exercise 16.6(a)

SLP §16.6, pp. 493–494. A pure exchange economy on `S = ℓ∞` with one household and one firm. The
book indexes time from `t = 1`; here `t : ℕ` starts at `0`, so the book's period `t` is our
`t − 1`, and every `2^{−t}` of the book is `pecW t = 2^{−(t+1)}`:

* `X = ℓ∞⁺` (`pecX`), `u(x) = Σ_t 2^{−(t+1)} [1 − exp(−x_t 2^{t+1})]` (`pecU`, built from the
  one-period terms `pecTerm t s = w_t (1 − exp(−s / w_t))`, `w_t = 2^{−(t+1)}`);
* `Y = {y : y_t ≤ 2^{−(t+1)} ∀ t}` (`pecY`); `x* = y* = (½, ¼, ⅛, …)` (`pecStar`).

Results.
* `pecTerm` is nonnegative on `[0, ∞)`, bounded by `w_t`, strictly increasing and concave, with
  `pecTerm t w_t = w_t (1 − e⁻¹)`; `u(x) ≤ u(x′)` for `0 ≤ x ≤ x′`, strictly if some coordinate
  is strictly smaller (`pecUfun_le`, `pecUfun_lt`), and changing one coordinate changes `u` by
  the change in that term (`pecUfun_update`).
* **Exercise 16.6(a)** (`ex_16_6a`, p. 494): Assumptions 15.1–15.7 hold (`pec_assumption15_1`
  … `pec_assumption15_7`).
* The unique Pareto optimum is `x* = y*` (`pec_paretoOptimal_iff`), and the household is
  nonsatiated there (`pec_nonsatiated`); local nonsatiation holds (`pec_localNonsatiation`).

**Corrections (solutions manual, Exercise 16.6(a)).**
* *A15.3.* The manual chooses one `δ > 0` with `|x_t − x′_t| < δ ⇒
  |exp(−x′_t 2^t) − exp(−x_t 2^t)| < ε` for all `t` at once. No such `δ` exists, already for
  `ε = 1/2` (`pec_manual_uniform_delta_counterexample`): `s ↦ exp(−2^t s)` has slope `2^t` at `0`.
  The conclusion (continuity of `u` on `X`) is true: `pec_assumption15_3` proves it by the
  Weierstrass M-test (each term is continuous and bounded by `w_t` on `X`), which is the
  truncation repair of the transcription's NOTE. `u` is nevertheless not Lipschitz on `X`
  (`pec_not_lipschitz`: `u(δ𝟙) − u(0) ≥ (n + 1) δ / 2` for `δ = 2^{−(n+1)}`), so no argument with
  a modulus linear in `‖x − x′‖` can work.
* *A15.7.* The manual picks `T*` with `2^{−(T*+1)} < ε` and then asserts
  `Σ_{t ≥ T+1} 2^{−t} < ε` for `T ≥ T*`; at `T = T*` the tail is `2^{−T*}`, which can equal `ε`
  (`pec_manual_tail_offbyone`). The off-by-one is harmless: since `ε < u(x) − u(x′)` strictly,
  `u(x) − u(xᵀ) ≤ ε` already gives `u(xᵀ) > u(x′)`. `pec_assumption15_7` proves 15.7 from
  `u(xᵀ) → u(x)`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

/-! ### The one-period terms -/

/-- The weight `w_t = 2^{−(t+1)}` (the book's `2^{−t}` for its period `t + 1`). -/
noncomputable def pecW (t : ℕ) : ℝ := (1 / 2 : ℝ) ^ (t + 1)

/-- `w_t > 0`. -/
theorem pecW_pos (t : ℕ) : 0 < pecW t := by unfold pecW; positivity

/-- `w_t ≤ 1/2`. -/
theorem pecW_le_half (t : ℕ) : pecW t ≤ 1 / 2 := by
  unfold pecW
  rw [pow_succ]
  have : (1 / 2 : ℝ) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-- `Σ_t w_t = 1`. -/
theorem hasSum_pecW : HasSum pecW 1 := by
  have h := hasSum_geometric_two.mul_left (1 / 2 : ℝ)
  have he : (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2) ^ n) = pecW := by
    funext n; unfold pecW; rw [pow_succ']
  rw [he] at h
  simpa using h

/-- `w_t` is summable. -/
theorem summable_pecW : Summable pecW := hasSum_pecW.summable

/-- `w_t → 0`. -/
theorem tendsto_pecW : Tendsto pecW atTop (𝓝 0) := summable_pecW.tendsto_atTop_zero

/-- The period-`t` utility term `w_t (1 − exp(−s / w_t))` (the book's
`2^{−t}[1 − exp(−x_t 2^t)]`). -/
noncomputable def pecTerm (t : ℕ) (s : ℝ) : ℝ := pecW t * (1 - Real.exp (-(s / pecW t)))

/-- `pecTerm t 0 = 0`. -/
@[simp] theorem pecTerm_zero (t : ℕ) : pecTerm t 0 = 0 := by simp [pecTerm]

/-- `pecTerm t s ≥ 0` for `s ≥ 0`. -/
theorem pecTerm_nonneg (t : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pecTerm t s := by
  unfold pecTerm
  have : Real.exp (-(s / pecW t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hs (pecW_pos t).le))
  have := pecW_pos t
  nlinarith

/-- `pecTerm t s < w_t`. -/
theorem pecTerm_lt (t : ℕ) (s : ℝ) : pecTerm t s < pecW t := by
  unfold pecTerm
  have := Real.exp_pos (-(s / pecW t))
  have := pecW_pos t
  nlinarith

/-- `pecTerm t` is continuous. -/
theorem continuous_pecTerm (t : ℕ) : Continuous (pecTerm t) := by
  unfold pecTerm; fun_prop

/-- `pecTerm t` is strictly increasing. -/
theorem pecTerm_strictMono (t : ℕ) : StrictMono (pecTerm t) := fun s s' h => by
  unfold pecTerm
  have hw := pecW_pos t
  have : Real.exp (-(s' / pecW t)) < Real.exp (-(s / pecW t)) :=
    Real.exp_lt_exp.2 (neg_lt_neg (div_lt_div_of_pos_right h hw))
  nlinarith

/-- `pecTerm t` is concave. -/
theorem pecTerm_concave (t : ℕ) (s s' : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * pecTerm t s + (1 - θ) * pecTerm t s' ≤ pecTerm t (θ * s + (1 - θ) * s') := by
  unfold pecTerm
  have hw := pecW_pos t
  have hc := convexOn_exp.2 (mem_univ (-(s / pecW t))) (mem_univ (-(s' / pecW t))) h0
    (by linarith : 0 ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  have he : θ * -(s / pecW t) + (1 - θ) * -(s' / pecW t) = -((θ * s + (1 - θ) * s') / pecW t) := by
    field_simp; ring
  rw [he] at hc
  nlinarith

/-- `pecTerm t w_t = w_t (1 − e⁻¹)`: at `x*` every marginal utility is `e⁻¹`. -/
theorem pecTerm_pecW (t : ℕ) : pecTerm t (pecW t) = pecW t * (1 - Real.exp (-1)) := by
  unfold pecTerm; rw [div_self (pecW_pos t).ne']

/-! ### The utility function -/

/-- `u` on sequences: `u(f) = Σ_t pecTerm t (f t)`. -/
noncomputable def pecUfun (f : ℕ → ℝ) : ℝ := ∑' t, pecTerm t (f t)

/-- The series defining `u` converges for nonnegative sequences, with terms in `[0, w_t]`. -/
theorem hasSum_pecUfun {f : ℕ → ℝ} (hf : ∀ t, 0 ≤ f t) :
    HasSum (fun t => pecTerm t (f t)) (pecUfun f) :=
  (Summable.of_nonneg_of_le (fun t => pecTerm_nonneg t (hf t)) (fun t => (pecTerm_lt t _).le)
    summable_pecW).hasSum

/-- `u` is monotone on nonnegative sequences. -/
theorem pecUfun_le {f g : ℕ → ℝ} (hf : ∀ t, 0 ≤ f t) (hfg : ∀ t, f t ≤ g t) :
    pecUfun f ≤ pecUfun g :=
  hasSum_le (fun t => (pecTerm_strictMono t).monotone (hfg t)) (hasSum_pecUfun hf)
    (hasSum_pecUfun fun t => (hf t).trans (hfg t))

/-- `u` is strictly monotone on nonnegative sequences. -/
theorem pecUfun_lt {f g : ℕ → ℝ} (hf : ∀ t, 0 ≤ f t) (hfg : ∀ t, f t ≤ g t) {t : ℕ}
    (ht : f t < g t) : pecUfun f < pecUfun g :=
  hasSum_lt (f := fun t => pecTerm t (f t)) (g := fun t => pecTerm t (g t))
    (fun t => (pecTerm_strictMono t).monotone (hfg t)) (pecTerm_strictMono t ht)
    (hasSum_pecUfun hf) (hasSum_pecUfun fun t => (hf t).trans (hfg t))

/-- Changing one coordinate changes `u` by the change in that period's term. -/
theorem pecUfun_update {f : ℕ → ℝ} (hf : ∀ t, 0 ≤ f t) (t : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    pecUfun (Function.update f t v) = pecUfun f + (pecTerm t v - pecTerm t (f t)) := by
  have hg : ∀ q, 0 ≤ Function.update f t v q := fun q => by
    rcases eq_or_ne q t with rfl | hq
    · simpa using hv
    · simpa [Function.update_of_ne hq] using hf q
  have h := (hasSum_pecUfun hf).add (hasSum_pi_single t (pecTerm t v - pecTerm t (f t)))
  refine (hasSum_pecUfun hg).unique (h.congr_fun fun q => ?_)
  rcases eq_or_ne q t with rfl | hq
  · simp
  · simp [Function.update_of_ne hq, Pi.single_eq_of_ne hq]

/-- `u(x*) = 1 − e⁻¹`. -/
theorem pecUfun_pecW : pecUfun pecW = 1 - Real.exp (-1) := by
  have h := (hasSum_pecUfun fun t => (pecW_pos t).le)
  simp only [pecTerm_pecW] at h
  have h' := hasSum_pecW.mul_right (1 - Real.exp (-1))
  rw [one_mul] at h'
  exact h.unique h'

/-! ### The economy -/

/-- The consumption set `X = ℓ∞⁺`. -/
def pecX : Set (BddSeq ℝ) := {x | ∀ t, 0 ≤ x t}

/-- The utility function `u(x) = Σ_t 2^{−(t+1)} [1 − exp(−x_t 2^{t+1})]` (p. 493). -/
noncomputable def pecU (x : BddSeq ℝ) : ℝ := pecUfun x

/-- The production set `Y = {y : y_t ≤ 2^{−(t+1)} ∀ t}` (p. 494). -/
def pecY : Set (BddSeq ℝ) := {y | ∀ t, y t ≤ pecW t}

/-- The Pareto optimum `x* = y* = (½, ¼, ⅛, …)` (p. 494). -/
noncomputable def pecStar : BddSeq ℝ :=
  BddSeq.mk pecW 1 fun t => by
    rw [Real.norm_eq_abs, abs_of_pos (pecW_pos t)]; linarith [pecW_le_half t]

/-- Coordinates of `x*`. -/
@[simp] theorem pecStar_apply (t : ℕ) : pecStar t = pecW t := rfl

/-- `u(x*) = 1 − e⁻¹`. -/
theorem pecU_pecStar : pecU pecStar = 1 - Real.exp (-1) := pecUfun_pecW

/-- `x* ∈ X`. -/
theorem pecStar_mem_pecX : pecStar ∈ pecX := fun t => (pecW_pos t).le

/-- `x* ∈ Y`. -/
theorem pecStar_mem_pecY : pecStar ∈ pecY := fun _ => le_rfl

/-- Coordinates of `x + a eₜ`. -/
theorem pec_add_single_apply (x : BddSeq ℝ) (t : ℕ) (a : ℝ) (q : ℕ) :
    (x + (lp.single ∞ t a : BddSeq ℝ)) q = Function.update (⇑x) t (x t + a) q := by
  rw [lp.coeFn_add, Pi.add_apply, lp.single_apply]
  rcases eq_or_ne q t with rfl | hq
  · simp
  · simp [Function.update_of_ne hq, Pi.single_eq_of_ne hq]

/-- `u(x + a eₜ) = u(x) + [pecTerm t (x_t + a) − pecTerm t x_t]` for `x ≥ 0`, `x_t + a ≥ 0`. -/
theorem pecU_add_single {x : BddSeq ℝ} (hx : x ∈ pecX) (t : ℕ) {a : ℝ} (ha : 0 ≤ x t + a) :
    pecU (x + (lp.single ∞ t a : BddSeq ℝ)) = pecU x + (pecTerm t (x t + a) - pecTerm t (x t)) := by
  have he : ⇑(x + (lp.single ∞ t a : BddSeq ℝ)) = Function.update (⇑x) t (x t + a) :=
    funext (pec_add_single_apply x t a)
  unfold pecU
  rw [he]
  exact pecUfun_update hx t ha

/-- `u` is strictly increasing on `X`: `0 ≤ x ≤ x′` with `x_t < x′_t` gives `u(x) < u(x′)`. -/
theorem pecU_lt {x x' : BddSeq ℝ} (hx : x ∈ pecX) (hle : ∀ t, x t ≤ x' t) {t : ℕ}
    (ht : x t < x' t) : pecU x < pecU x' :=
  pecUfun_lt hx hle ht

/-- The aggregate technology of the one-firm economy is `Y`. -/
theorem pec_aggTech : aggTech (fun _ : Unit => pecY) = pecY := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

/-! ### Exercise 16.6(a): Assumptions 15.1–15.7 -/

/-- **Assumption 15.1**: `X = ℓ∞⁺` is convex. -/
theorem pec_assumption15_1 : Assumption15_1 (fun _ : Unit => pecX) :=
  fun _ x hx x' hx' a b ha hb _ t => by
    rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
    have := hx t; have := hx' t
    positivity

/-- **Assumption 15.2**: `u` is concave on `X`, hence semistrictly quasi-concave. -/
theorem pec_assumption15_2 : Assumption15_2 (fun _ : Unit => pecX) (fun _ : Unit => pecU) :=
  fun _ => SeqSemistrictQC.of_concave fun z hz z' hz' θ h0 h1 => by
    have hzz : ∀ t, 0 ≤ (θ • z + (1 - θ) • z') t := fun t => by
      rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
      have := hz t; have := hz' t
      have : 0 ≤ 1 - θ := by linarith
      positivity
    have hs := ((hasSum_pecUfun hz).mul_left θ).add ((hasSum_pecUfun hz').mul_left (1 - θ))
    refine hasSum_le (fun t => ?_) hs (hasSum_pecUfun hzz)
    change θ * pecTerm t (z t) + (1 - θ) * pecTerm t (z' t) ≤
      pecTerm t ((θ • z + (1 - θ) • z') t)
    rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
    exact pecTerm_concave t _ _ h0.le h1.le

/-- **Assumption 15.3**: `u` is continuous on `X`, by the Weierstrass M-test (each term is
continuous and bounded by `w_t` on `X`). -/
theorem pec_assumption15_3 : Assumption15_3 (fun _ : Unit => pecX) (fun _ : Unit => pecU) :=
  fun _ => continuousOn_tsum (u := pecW)
    (fun t => ((continuous_pecTerm t).comp (continuous_seq_coord t)).continuousOn) summable_pecW
    fun t x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pecTerm_nonneg t (hx t))]
      exact (pecTerm_lt t _).le

/-- **Assumption 15.4**: the aggregate technology `Y` is convex. -/
theorem pec_assumption15_4 : Assumption15_4 (fun _ : Unit => pecY) := by
  unfold Assumption15_4
  rw [pec_aggTech]
  intro y hy y' hy' a b ha hb hab t
  rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hy t) ha
  have h2 := mul_le_mul_of_nonneg_left (hy' t) hb
  have : a * pecW t + b * pecW t = pecW t := by rw [← add_mul, hab, one_mul]
  linarith

/-- **Assumption 15.5**: `Y` has an interior point, `−𝟙` (it contains the negative orthant). -/
theorem pec_assumption15_5 : Assumption15_5 (BddSeq ℝ) (fun _ : Unit => pecY) := by
  left
  rw [pec_aggTech]
  refine ⟨-oneSeq, mem_interior.2 ⟨Metric.ball (-oneSeq) 1, fun y hy t => ?_,
    Metric.isOpen_ball, Metric.mem_ball_self one_pos⟩⟩
  have h := (norm_seq_coord_le (y - -oneSeq) t).trans_lt (by rwa [← dist_eq_norm])
  rw [lp.coeFn_sub, lp.coeFn_neg, Pi.sub_apply, Pi.neg_apply] at h
  have h' := (abs_lt.1 (by simpa using h)).2
  simp [oneSeq] at h'
  linarith [pecW_pos t]

/-- **Assumption 15.6**: truncations of points of `X` and of `Y` stay in `X` and `Y`. -/
theorem pec_assumption15_6 : Assumption15_6 (fun _ : Unit => pecX) (fun _ : Unit => pecY) :=
  ⟨fun _ x hx => Eventually.of_forall fun T t => by
      rw [seqTrunc_apply]; split_ifs
      · exact hx t
      · exact le_rfl,
    fun _ y hy => Eventually.of_forall fun T t => by
      rw [seqTrunc_apply]; split_ifs
      · exact hy t
      · exact (pecW_pos t).le⟩

/-- `u(xᵀ)` is the `T`-th partial sum of the series for `u(x)`. -/
theorem pecU_seqTrunc (T : ℕ) (x : BddSeq ℝ) :
    pecU (seqTrunc T x) = ∑ t ∈ Finset.range (T + 1), pecTerm t (x t) := by
  unfold pecU pecUfun
  rw [tsum_eq_sum (s := Finset.range (T + 1)) fun t ht => by
    have : ¬ t ≤ T := by simpa [Nat.lt_succ_iff] using ht
    simp [seqTrunc_apply, this]]
  refine Finset.sum_congr rfl fun t ht => ?_
  have : t ≤ T := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  simp [seqTrunc_apply, this]

/-- **Assumption 15.7**: `u(xᵀ) → u(x)` on `X`. -/
theorem pec_assumption15_7 : Assumption15_7 (fun _ : Unit => pecX) (fun _ : Unit => pecU) :=
  fun _ => SeqTailInsensitive.of_tendsto fun x hx => by
    simp only [pecU_seqTrunc]
    exact (hasSum_pecUfun hx).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- **Exercise 16.6(a)** (p. 494): the economy of §16.6 satisfies Assumptions 15.1–15.7. -/
theorem ex_16_6a :
    Assumption15_1 (fun _ : Unit => pecX) ∧
    Assumption15_2 (fun _ : Unit => pecX) (fun _ : Unit => pecU) ∧
    Assumption15_3 (fun _ : Unit => pecX) (fun _ : Unit => pecU) ∧
    Assumption15_4 (fun _ : Unit => pecY) ∧
    Assumption15_5 (BddSeq ℝ) (fun _ : Unit => pecY) ∧
    Assumption15_6 (fun _ : Unit => pecX) (fun _ : Unit => pecY) ∧
    Assumption15_7 (fun _ : Unit => pecX) (fun _ : Unit => pecU) :=
  ⟨pec_assumption15_1, pec_assumption15_2, pec_assumption15_3, pec_assumption15_4,
    pec_assumption15_5, pec_assumption15_6, pec_assumption15_7⟩

/-! ### The Pareto optimum -/

/-- Feasibility in the one-household, one-firm economy: `x ∈ X`, `x ∈ Y`, and `y = x`. -/
theorem pec_feasible_iff (x y : Unit → BddSeq ℝ) :
    Feasible (fun _ : Unit => pecX) (fun _ : Unit => pecY) x y ↔
      x () ∈ pecX ∧ x () ∈ pecY ∧ y () = x () := by
  simp only [Feasible, Finset.univ_unique, Finset.sum_singleton]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    have he : x () = y () := sub_eq_zero.1 (by simpa using hxy)
    exact ⟨hx (), he ▸ hy (), he.symm⟩
  · rintro ⟨hx, hy, he⟩
    refine ⟨fun i => by cases i; exact hx, fun j => by cases j; rw [he]; exact hy, ?_⟩
    simp [he]

/-- A feasible consumption is at most `x*`, so its utility is at most `u(x*)`. -/
theorem pecU_le_of_mem {x : BddSeq ℝ} (hx : x ∈ pecX) (hy : x ∈ pecY) : pecU x ≤ pecU pecStar :=
  pecUfun_le hx fun t => hy t

/-- **The unique Pareto optimum is `x* = y*`** (p. 494). -/
theorem pec_paretoOptimal_iff (x y : Unit → BddSeq ℝ) :
    ParetoOptimal (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY) x y ↔
      x () = pecStar ∧ y () = pecStar := by
  have hstar : Feasible (fun _ : Unit => pecX) (fun _ : Unit => pecY) (fun _ => pecStar)
      (fun _ => pecStar) := (pec_feasible_iff _ _).2 ⟨pecStar_mem_pecX, pecStar_mem_pecY, rfl⟩
  constructor
  · rintro ⟨hF, hno⟩
    obtain ⟨hx, hy, he⟩ := (pec_feasible_iff x y).1 hF
    have hxs : x () = pecStar := by
      by_contra hne
      have : ∃ t, x () t ≠ pecW t := by
        by_contra hall
        push Not at hall
        exact hne (by ext t; exact hall t)
      obtain ⟨t, ht⟩ := this
      have hlt : pecU (x ()) < pecU pecStar :=
        pecU_lt hx (fun q => hy q) (lt_of_le_of_ne (hy t) ht)
      exact hno ⟨fun _ => pecStar, fun _ => pecStar, hstar, fun i => by cases i; exact hlt.le,
        (), hlt⟩
    exact ⟨hxs, he.trans hxs⟩
  · rintro ⟨hx, hy⟩
    have hxf : x = fun _ => pecStar := funext fun i => by cases i; exact hx
    have hyf : y = fun _ => pecStar := funext fun i => by cases i; exact hy
    subst hxf hyf
    refine ⟨hstar, ?_⟩
    rintro ⟨x', y', hF', -, i, hi⟩
    obtain ⟨hx', hy', -⟩ := (pec_feasible_iff x' y').1 hF'
    cases i
    exact absurd hi (not_lt.2 (pecU_le_of_mem hx' hy'))

/-- `x* + e₀ ∈ X` is strictly preferred to `x*`: the household is nonsatiated at `x*`. -/
theorem pec_nonsatiated :
    pecStar + (lp.single ∞ 0 1 : BddSeq ℝ) ∈ pecX ∧
      pecU pecStar < pecU (pecStar + (lp.single ∞ 0 1 : BddSeq ℝ)) := by
  refine ⟨fun q => ?_, pecU_lt pecStar_mem_pecX (t := 0) (fun q => ?_) ?_⟩
  · rw [pec_add_single_apply]
    rcases eq_or_ne q 0 with rfl | hq
    · simp; linarith [pecW_pos 0]
    · simp [Function.update_of_ne hq, (pecW_pos q).le]
  · rw [pec_add_single_apply]
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    · simp [Function.update_of_ne hq]
  · rw [pec_add_single_apply]; simp

/-- **Local nonsatiation** (the hypothesis of Theorem 15.3): `z + e₀/(n + 1) → z` is strictly
preferred to `z` for every `z ∈ X`. -/
theorem pec_localNonsatiation : LocalNonsatiation (fun _ : Unit => pecX) (fun _ : Unit => pecU) :=
  fun _ z hz => by
    have hmem : ∀ n : ℕ, ∀ q, 0 ≤ (z + (lp.single ∞ 0 (1 / ((n : ℝ) + 1)) : BddSeq ℝ)) q := by
      intro n q
      rw [pec_add_single_apply]
      rcases eq_or_ne q 0 with rfl | hq
      · simp only [Function.update_self]; have := hz 0; positivity
      · simp [Function.update_of_ne hq, hz q]
    refine ⟨fun n => z + (lp.single ∞ 0 (1 / ((n : ℝ) + 1)) : BddSeq ℝ), hmem, ?_, fun n => ?_⟩
    · have h := (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) ∞ 0).continuous.tendsto 0
      have h2 := tendsto_const_nhds (x := z) |>.add
        (h.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      simpa using h2
    · refine pecU_lt hz (t := 0) (fun q => ?_) ?_
      · rw [pec_add_single_apply]
        rcases eq_or_ne q 0 with rfl | hq
        · simp only [Function.update_self]; have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
          linarith
        · simp [Function.update_of_ne hq]
      · rw [pec_add_single_apply]; simp only [Function.update_self]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith

/-! ### The manual's proofs of A15.3 and A15.7 -/

/-- **The manual's uniform `δ` for A15.3 does not exist.** There is no `δ > 0` such that
`|s − s′| < δ` implies `|exp(−s′ 2^{t+1}) − exp(−s 2^{t+1})| < 1/2` for all `t` and all
`s, s′ ≥ 0`. -/
theorem pec_manual_uniform_delta_counterexample :
    ¬ ∃ δ > 0, ∀ t : ℕ, ∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → |s - s'| < δ →
      |Real.exp (-(s' / pecW t)) - Real.exp (-(s / pecW t))| < 1 / 2 := by
  rintro ⟨δ, hδ, h⟩
  obtain ⟨t, ht⟩ := (tendsto_pecW.eventually (gt_mem_nhds (half_pos hδ))).exists
  have hw := pecW_pos t
  have hab : |(0 : ℝ) - δ / 2| < δ := by
    rw [zero_sub, abs_neg, abs_of_pos (half_pos hδ)]
    linarith
  have h1 := h t 0 (δ / 2) le_rfl (by positivity) hab
  have hge : 1 ≤ δ / 2 / pecW t := (one_le_div hw).2 ht.le
  have hexp : Real.exp (-(δ / 2 / pecW t)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have he1 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  rw [zero_div, neg_zero, Real.exp_zero] at h1
  have hpos := Real.exp_pos (-(δ / 2 / pecW t))
  rw [abs_of_neg (by linarith)] at h1
  linarith

/-- **The manual's off-by-one in A15.7.** With `ε = 2^{−T}` (book indexing: `ε = 2^{−T*}`), the
manual's choice condition `2^{−(T+1)} < ε` holds, yet the tail `Σ_{t ≥ T} w_t` (the book's
`Σ_{t ≥ T*+1} 2^{−t}`) equals `ε` and is not `< ε`. -/
theorem pec_manual_tail_offbyone (T : ℕ) :
    (1 / 2 : ℝ) ^ (T + 1) < (1 / 2) ^ T ∧ ∑' t, pecW (t + T) = (1 / 2) ^ T := by
  refine ⟨pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self T), ?_⟩
  have h := hasSum_pecW.mul_left ((1 / 2 : ℝ) ^ T)
  rw [mul_one] at h
  refine (h.congr_fun fun t => ?_).tsum_eq
  unfold pecW
  rw [← pow_add]
  ring_nf

/-- The bound `1 − e^{−a} ≥ a/2` for `0 ≤ a ≤ 1` (from `e^a ≥ 1 + a`). -/
theorem pec_one_sub_exp_neg_ge {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    a / 2 ≤ 1 - Real.exp (-a) := by
  have h := Real.add_one_le_exp a
  have hm : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-a)
  nlinarith

/-- **`u` is not Lipschitz on `X`** (so the manual's A15.3 argument, which gives a modulus linear
in `‖x − x′‖`, cannot be repaired by a better constant): for `δ = 2^{−(n+1)}`,
`u(δ 𝟙) − u(0) ≥ (n + 1) δ / 2`. -/
theorem pec_not_lipschitz :
    ¬ ∃ L : ℝ, ∀ x ∈ pecX, ∀ x' ∈ pecX, |pecU x - pecU x'| ≤ L * ‖x - x'‖ := by
  rintro ⟨L, hL⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * L)
  set δ := pecW n with hδ
  have hδpos : 0 < δ := pecW_pos n
  set x : BddSeq ℝ := δ • oneSeq with hx
  have hxt : ∀ t, x t = δ := fun t => by simp [hx, oneSeq]
  have hxX : x ∈ pecX := fun t => by rw [hxt]; exact hδpos.le
  have h0X : (0 : BddSeq ℝ) ∈ pecX := fun t => le_rfl
  have hu0 : pecU 0 = 0 := by simp [pecU, pecUfun]
  have hnorm : ‖x - 0‖ ≤ δ := by
    rw [sub_zero, hx, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    exact mul_le_of_le_one_right hδpos.le norm_oneSeq_le
  have hterm : ∀ t ∈ Finset.range (n + 1), δ / 2 ≤ pecTerm t (x t) := fun t ht => by
    have htn : t ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    have hw := pecW_pos t
    have hle : δ ≤ pecW t := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have ha0 : 0 ≤ δ / pecW t := div_nonneg hδpos.le hw.le
    have ha1 : δ / pecW t ≤ 1 := (div_le_one hw).2 hle
    have := pec_one_sub_exp_neg_ge ha0 ha1
    rw [hxt]
    unfold pecTerm
    have hmul : pecW t * (δ / pecW t / 2) = δ / 2 := by field_simp
    nlinarith
  have hsum : (n + 1 : ℝ) * (δ / 2) ≤ pecU x := by
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have h2 := sum_le_hasSum (Finset.range (n + 1)) (fun t _ => pecTerm_nonneg t (hxX t))
      (hasSum_pecUfun hxX)
    push_cast at h1
    exact h1.trans h2
  have hlip := hL x hxX 0 h0X
  rw [hu0, sub_zero] at hlip
  have hux : 0 ≤ pecU x := (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ) * (δ / 2)).trans hsum
  rw [abs_of_nonneg hux] at hlip
  have hL0 : 0 ≤ L := by
    by_contra hneg
    push Not at hneg
    have : L * ‖x - 0‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (norm_nonneg _)
    nlinarith
  have := hlip.trans (mul_le_mul_of_nonneg_left hnorm hL0)
  nlinarith

end StokeyLucasPrescott.EquilibriumApplications

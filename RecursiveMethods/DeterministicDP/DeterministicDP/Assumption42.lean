/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.Principle

/-!
# When the sequence problem is well defined

SLP §4.1, pp. 67–69: sufficient conditions for Assumption 4.2, and Exercises 4.1–4.2.

* `tendsto_of_summable_pos`, `tendsto_of_summable_neg`: partial sums converge in `R̄` when the
  positive (or the negative) parts are summable.
* `assumption42_of_summable_pos`, `assumption42_of_summable_neg` (p. 69): Assumption 4.2 holds if
  `lim Σ βᵗF⁺ < ∞` or `lim Σ βᵗF⁻ < ∞` along every feasible plan.
* `assumption42_of_bddAbove`, `assumption42_of_bddBelow`: `F` bounded above or below and
  `0 ≤ β < 1`.
* `assumption42_of_geometric`: `F(x_t, x_{t+1}) ≤ cθᵗ` with `θ < 1/β`.
* `ex_4_2a`, `ex_4_2b`: two sets of conditions on `F` and `Γ` over `ℝˡ₊`.
* `ex_4_1a`, `ex_4_1b`: the one-sector and many-sector growth models as sequence problems.
-/

open Filter Topology Finset

namespace StokeyLucasPrescott.DeterministicDP

/-- Partial sums of a real sequence converge in `R̄` if the positive parts are summable. -/
theorem tendsto_of_summable_pos (a : ℕ → ℝ) (h : Summable fun t => max (a t) 0) :
    ∃ L : EReal, Tendsto (fun n => ((∑ t ∈ range (n + 1), a t : ℝ) : EReal)) atTop (𝓝 L) := by
  set P : ℕ → ℝ := fun n => ∑ t ∈ range (n + 1), max (a t) 0
  set N : ℕ → ℝ := fun n => ∑ t ∈ range (n + 1), max (-a t) 0
  have hP : Tendsto P atTop (𝓝 (∑' t, max (a t) 0)) :=
    h.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hNmono : Monotone fun n => ((N n : ℝ) : EReal) := fun m n hmn => by
    refine EReal.coe_le_coe_iff.2 (sum_le_sum_of_subset_of_nonneg
      (range_subset_range.2 (by omega)) fun _ _ _ => le_max_right _ _)
  have hN := tendsto_atTop_iSup hNmono
  have hsplit : ∀ n, ((∑ t ∈ range (n + 1), a t : ℝ) : EReal) =
      ((P n : ℝ) : EReal) + -((N n : ℝ) : EReal) := fun n => by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    simp only [P, N, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rcases le_total (a t) 0 with h0 | h0
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  refine ⟨((∑' t, max (a t) 0 : ℝ) : EReal) + -(⨆ n, ((N n : ℝ) : EReal)), ?_⟩
  simp only [hsplit]
  refine Tendsto.comp (f := fun n => (((P n : ℝ) : EReal), -((N n : ℝ) : EReal)))
    (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))
    ((EReal.tendsto_coe.2 hP).prodMk_nhds (continuous_neg.tendsto _ |>.comp hN))

/-- Partial sums of a real sequence converge in `R̄` if the negative parts are summable. -/
theorem tendsto_of_summable_neg (a : ℕ → ℝ) (h : Summable fun t => max (-a t) 0) :
    ∃ L : EReal, Tendsto (fun n => ((∑ t ∈ range (n + 1), a t : ℝ) : EReal)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := tendsto_of_summable_pos (fun t => -a t) h
  refine ⟨-L, ?_⟩
  have := (continuous_neg.tendsto L).comp hL
  refine this.congr fun n => ?_
  simp [sum_neg_distrib]

variable {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

/-- **p. 69.** Assumption 4.2 holds if `Σ βᵗF⁺(x_t, x_{t+1}) < ∞` along every feasible plan. -/
theorem assumption42_of_summable_pos
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, Summable fun t => max (β ^ t * F (x t) (x (t + 1))) 0) :
    Assumption42 Γ F β := fun x₀ x hx => tendsto_of_summable_pos _ (h x₀ x hx)

/-- **p. 69.** Assumption 4.2 holds if `Σ βᵗF⁻(x_t, x_{t+1}) < ∞` along every feasible plan. -/
theorem assumption42_of_summable_neg
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, Summable fun t => max (-(β ^ t * F (x t) (x (t + 1)))) 0) :
    Assumption42 Γ F β := fun x₀ x hx => tendsto_of_summable_neg _ (h x₀ x hx)

/-- Positive multiples of a geometric bound are summable. -/
theorem summable_max_of_le_geometric {b : ℕ → ℝ} {c r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hc : 0 ≤ c) (hb : ∀ t, b t ≤ c * r ^ t) : Summable fun t => max (b t) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun t => max_le (hb t) (mul_nonneg hc (pow_nonneg hr0 t)))
    ((summable_geometric_of_lt_one hr0 hr).mul_left c)

/-- **p. 69.** `F` bounded above and `0 ≤ β < 1`. -/
theorem assumption42_of_bddAbove {M : ℝ} (hF : ∀ x y, F x y ≤ M) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Assumption42 Γ F β :=
  assumption42_of_summable_pos fun _ x _ =>
    summable_max_of_le_geometric hβ0 hβ1 (le_max_right M 0) fun t => by
      rw [mul_comm (max M 0)]
      exact mul_le_mul_of_nonneg_left ((hF _ _).trans (le_max_left _ _)) (pow_nonneg hβ0 t)

/-- **p. 69.** `F` bounded below and `0 ≤ β < 1`. -/
theorem assumption42_of_bddBelow {M : ℝ} (hF : ∀ x y, M ≤ F x y) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Assumption42 Γ F β :=
  assumption42_of_summable_neg fun _ x _ =>
    summable_max_of_le_geometric hβ0 hβ1 (le_max_right (-M) 0) fun t => by
      have := mul_le_mul_of_nonneg_left
        ((neg_le_neg (hF (x t) (x (t + 1)))).trans (le_max_left (-M) 0)) (pow_nonneg hβ0 t)
      linarith

/-- **p. 69.** If along every feasible plan `F(x_t, x_{t+1}) ≤ cθᵗ` for some `0 < θ < 1/β` and
`c > 0`, Assumption 4.2 holds (`β > 0`). -/
theorem assumption42_of_geometric (hβ : 0 < β)
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∃ θ c : ℝ, 0 < θ ∧ θ < β⁻¹ ∧ 0 < c ∧
      ∀ t, F (x t) (x (t + 1)) ≤ c * θ ^ t) :
    Assumption42 Γ F β :=
  assumption42_of_summable_pos fun x₀ x hx => by
    obtain ⟨θ, c, hθ, hθβ, hc, hF⟩ := h x₀ x hx
    have hβθ : β * θ < 1 := by
      calc β * θ < β * β⁻¹ := mul_lt_mul_of_pos_left hθβ hβ
        _ = 1 := mul_inv_cancel₀ hβ.ne'
    refine summable_max_of_le_geometric (mul_nonneg hβ.le hθ.le) hβθ hc.le fun t => ?_
    rw [mul_pow, mul_comm c, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hF t).trans_eq (mul_comm _ _)) (pow_nonneg hβ.le t)

/-! ### Exercise 4.2: problems on `ℝˡ₊` -/

/-- The nonnegative orthant `ℝˡ₊`. -/
abbrev Orthant (l : ℕ) := {x : Fin l → ℝ // 0 ≤ x}

variable {l : ℕ}

/-- `θx + (1 − θ)x'` in `ℝˡ₊` for `θ ∈ [0, 1]`. -/
def orthCombo (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x x' : Orthant l) : Orthant l :=
  ⟨θ • x.1 + (1 - θ) • x'.1, add_nonneg (smul_nonneg hθ0 x.2) (smul_nonneg (by linarith) x'.2)⟩

/-- The origin of `ℝˡ₊`. -/
def orthZero (l : ℕ) : Orthant l := ⟨0, le_rfl⟩

/-- The vector `(1, …, 1)`. -/
def orthOne (l : ℕ) : Orthant l := ⟨1, zero_le_one⟩

/-- Along a plan with `‖x_{t+1}‖ ≤ θ‖x_t‖`, `‖x_t‖ ≤ θᵗ‖x₀‖`. -/
theorem norm_le_geometric {Γ : Orthant l → Set (Orthant l)} {θ : ℝ} (hθ : 0 ≤ θ)
    (hΓ : ∀ x, ∀ y ∈ Γ x, ‖y.1‖ ≤ θ * ‖x.1‖) {x₀ : Orthant l} {x : ℕ → Orthant l}
    (hx : x ∈ Feasible Γ x₀) (t : ℕ) : ‖(x t).1‖ ≤ θ ^ t * ‖x₀.1‖ := by
  induction t with
  | zero => simp [hx.1]
  | succ t ih =>
    calc ‖(x (t + 1)).1‖ ≤ θ * ‖(x t).1‖ := hΓ _ _ (hx.2 t)
      _ ≤ θ * (θ ^ t * ‖x₀.1‖) := mul_le_mul_of_nonneg_left ih hθ
      _ = θ ^ (t + 1) * ‖x₀.1‖ := by ring

/-- **Exercise 4.2a.** On `X = ℝˡ₊` with `0 < β < 1`, Assumption 4.2 holds if for some
`0 < θ < 1/β`, `y ∈ Γ(x)` implies `‖y‖ ≤ θ‖x‖`; `F(0, 0) = 0`; and `F` is increasing and concave
in its first `l` arguments and decreasing in its last `l`. (The norm is the sup norm.) -/
theorem ex_4_2a {Γ : Orthant l → Set (Orthant l)} {F : Orthant l → Orthant l → ℝ} {θ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθβ : θ < β⁻¹)
    (hΓ : ∀ x, ∀ y ∈ Γ x, ‖y.1‖ ≤ θ * ‖x.1‖) (hF0 : F (orthZero l) (orthZero l) = 0)
    (hinc : ∀ y, Monotone fun x => F x y) (hdec : ∀ x, Antitone (F x))
    (hconc : ∀ y x x' (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1),
      s * F x y + (1 - s) * F x' y ≤ F (orthCombo s hs0 hs1 x x') y) :
    Assumption42 Γ F β := by
  set C := max (F (orthOne l) (orthZero l)) 0
  -- `F(x, 0) ≤ C max{1, ‖x‖}`
  have hle_one : ∀ z : Orthant l, ‖z.1‖ ≤ 1 → z ≤ orthOne l := fun z hz i =>
    ((Real.le_norm_self _).trans (norm_le_pi_norm z.1 i)).trans hz
  have hbound : ∀ z : Orthant l, F z (orthZero l) ≤ C * (1 + ‖z.1‖) := fun z => by
    have hC : 0 ≤ C := le_max_right _ _
    rcases le_or_gt ‖z.1‖ 1 with hz | hz
    · calc F z (orthZero l) ≤ F (orthOne l) (orthZero l) := hinc _ (hle_one z hz)
        _ ≤ C := le_max_left _ _
        _ ≤ C * (1 + ‖z.1‖) := le_mul_of_one_le_right hC (by linarith [norm_nonneg z.1])
    · set s := ‖z.1‖⁻¹
      have hs0 : 0 < s := inv_pos.2 (by linarith)
      have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ hz.le
      have hcomb := hconc (orthZero l) z (orthZero l) s hs0.le hs1
      rw [hF0, mul_zero, add_zero] at hcomb
      have hsmall : orthCombo s hs0.le hs1 z (orthZero l) ≤ orthOne l := by
        refine hle_one _ ?_
        simp only [orthCombo, orthZero, smul_zero, add_zero, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs0, s]
        rw [inv_mul_cancel₀ (by linarith)]
      have h1 : s * F z (orthZero l) ≤ C :=
        hcomb.trans ((hinc _ hsmall).trans (le_max_left _ _))
      have hz' : 0 < ‖z.1‖ := by linarith
      have e : ‖z.1‖ * s = 1 := mul_inv_cancel₀ hz'.ne'
      have h2 : F z (orthZero l) ≤ C * ‖z.1‖ := by
        calc F z (orthZero l) = (‖z.1‖ * s) * F z (orthZero l) := by rw [e, one_mul]
          _ = ‖z.1‖ * (s * F z (orthZero l)) := by ring
          _ ≤ ‖z.1‖ * C := mul_le_mul_of_nonneg_left h1 hz'.le
          _ = C * ‖z.1‖ := mul_comm _ _
      nlinarith
  refine assumption42_of_summable_pos fun x₀ x hx => ?_
  have hβθ : β * θ < 1 := by
    calc β * θ < β * β⁻¹ := mul_lt_mul_of_pos_left hθβ hβ0
      _ = 1 := mul_inv_cancel₀ hβ0.ne'
  have hC : 0 ≤ C := le_max_right _ _
  refine Summable.of_nonneg_of_le (fun t => le_max_right _ _) (fun t => ?_)
    (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left C).add
      ((summable_geometric_of_lt_one (mul_nonneg hβ0.le hθ0.le) hβθ).mul_left (C * ‖x₀.1‖)))
  refine max_le ?_ (by positivity)
  have h1 : F (x t) (x (t + 1)) ≤ F (x t) (orthZero l) := hdec _ (x (t + 1)).2
  have h2 := (hbound (x t)).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (norm_le_geometric hθ0.le hΓ hx t)) hC)
  calc β ^ t * F (x t) (x (t + 1)) ≤ β ^ t * (C * (1 + θ ^ t * ‖x₀.1‖)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hβ0.le t)
    _ = C * β ^ t + C * ‖x₀.1‖ * (β * θ) ^ t := by rw [mul_pow]; ring

/-- **Exercise 4.2b.** On `X = ℝˡ₊` with `0 < β < 1`, Assumption 4.2 holds if for some
`0 < θ < 1/β`, `y ∈ Γ(x)` implies `F(y, 0) ≤ θF(x, 0)`, and `F` is decreasing in its last `l`
arguments. (The book also assumes `F` increasing in its first `l` arguments and `0 ∈ Γ(x)`;
neither is needed.) -/
theorem ex_4_2b {Γ : Orthant l → Set (Orthant l)} {F : Orthant l → Orthant l → ℝ} {θ : ℝ}
    (hβ0 : 0 < β) (hθ0 : 0 < θ) (hθβ : θ < β⁻¹)
    (hΓ : ∀ x, ∀ y ∈ Γ x, F y (orthZero l) ≤ θ * F x (orthZero l))
    (hdec : ∀ x, Antitone (F x)) :
    Assumption42 Γ F β := by
  refine assumption42_of_geometric hβ0 fun x₀ x hx =>
    ⟨θ, |F x₀ (orthZero l)| + 1, hθ0, hθβ, by positivity, fun t => ?_⟩
  have hgeo : ∀ t, F (x t) (orthZero l) ≤ θ ^ t * F x₀ (orthZero l) := by
    intro t
    induction t with
    | zero => simp [hx.1]
    | succ t ih =>
      calc F (x (t + 1)) (orthZero l) ≤ θ * F (x t) (orthZero l) := hΓ _ _ (hx.2 t)
        _ ≤ θ * (θ ^ t * F x₀ (orthZero l)) := mul_le_mul_of_nonneg_left ih hθ0.le
        _ = θ ^ (t + 1) * F x₀ (orthZero l) := by ring
  calc F (x t) (x (t + 1)) ≤ F (x t) (orthZero l) := hdec _ (x (t + 1)).2
    _ ≤ θ ^ t * F x₀ (orthZero l) := hgeo t
    _ ≤ θ ^ t * (|F x₀ (orthZero l)| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [le_abs_self (F x₀ (orthZero l))])
          (pow_nonneg hθ0.le t)
    _ = (|F x₀ (orthZero l)| + 1) * θ ^ t := mul_comm _ _

/-! ### Exercise 4.1: growth models as sequence problems -/

/-- **Exercise 4.1a.** The one-sector growth model `max Σ βᵗU(f(k_t) − k_{t+1})`,
`0 ≤ k_{t+1} ≤ f(k_t)`, is the sequence problem with `Γ(k) = [0, f(k)]` and
`F(k, y) = U(f(k) − y)`: the plans are those of `Π(k₀)` and the objectives agree. -/
theorem ex_4_1a (U f : ℝ → ℝ) (k₀ : ℝ) (k : ℕ → ℝ) (n : ℕ) :
    (k ∈ Feasible (fun k => Set.Icc 0 (f k)) k₀ ↔
      k 0 = k₀ ∧ ∀ t, 0 ≤ k (t + 1) ∧ k (t + 1) ≤ f (k t)) ∧
    partialSum (fun k y => U (f k - y)) β k n =
      ∑ t ∈ range (n + 1), β ^ t * U (f (k t) - k (t + 1)) :=
  ⟨Iff.rfl, rfl⟩

/-- The many-sector technology: the consumption vectors `c ≥ 0` with `(k' + c, k) ∈ Y`. -/
def consSet {l : ℕ} (Y : Set ((Fin l → ℝ) × (Fin l → ℝ))) (k k' : Fin l → ℝ) :
    Set (Fin l → ℝ) :=
  {c | 0 ≤ c ∧ (k' + c, k) ∈ Y}

/-- **Exercise 4.1b.** The many-sector growth model `max Σ βᵗU(c_t)` subject to
`(k_{t+1} + c_t, k_t) ∈ Y`, `c_t ≥ 0`, is the sequence problem with
`Γ(k) = {k' : some c ≥ 0 has (k' + c, k) ∈ Y}` and `F(k, k') = max{U(c) : c ≥ 0, (k' + c, k) ∈ Y}`
(the maximum assumed attained): every plan `(c, k)` is dominated period by period by `F` along
`k`, and every `k ∈ Π(k₀)` is attained by some consumption plan. -/
theorem ex_4_1b {l : ℕ} (Y : Set ((Fin l → ℝ) × (Fin l → ℝ))) (U : (Fin l → ℝ) → ℝ)
    (F : (Fin l → ℝ) → (Fin l → ℝ) → ℝ) (hβ : 0 ≤ β)
    (hF : ∀ k k', ∀ c ∈ consSet Y k k', U c ≤ F k k')
    (hatt : ∀ k k', (consSet Y k k').Nonempty → ∃ c ∈ consSet Y k k', U c = F k k')
    (k₀ : Fin l → ℝ) :
    (∀ (c k : ℕ → (Fin l → ℝ)), k 0 = k₀ → (∀ t, c t ∈ consSet Y (k t) (k (t + 1))) →
      k ∈ Feasible (fun k => {k' | (consSet Y k k').Nonempty}) k₀ ∧
      ∀ n, ∑ t ∈ range (n + 1), β ^ t * U (c t) ≤ partialSum F β k n) ∧
    (∀ k ∈ Feasible (fun k => {k' | (consSet Y k k').Nonempty}) k₀, ∃ c : ℕ → (Fin l → ℝ),
      (∀ t, c t ∈ consSet Y (k t) (k (t + 1))) ∧
      ∀ n, ∑ t ∈ range (n + 1), β ^ t * U (c t) = partialSum F β k n) := by
  refine ⟨fun c k hk0 hc => ⟨⟨hk0, fun t => ⟨c t, hc t⟩⟩, fun n => ?_⟩, fun k hk => ?_⟩
  · exact sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hF _ _ _ (hc t)) (pow_nonneg hβ t)
  · choose c hc hU using fun t => hatt (k t) (k (t + 1)) (hk.2 t)
    exact ⟨c, hc, fun n => sum_congr rfl fun t _ => by rw [hU t]⟩

end StokeyLucasPrescott.DeterministicDP
